#!/usr/bin/python

import sys
import os
import math
import binascii
import hashlib
import random
import Crypto.Hash.SHA256
import Crypto.PublicKey.RSA
import Crypto.Cipher.PKCS1_v1_5
import Crypto.Cipher.PKCS1_OAEP
from Crypto.Util.strxor import strxor

RSAES_PKCS1_v1_5 = 0
RSAES_OAEP = 1
RSASSA_PKCS1_v1_5 = 10
RSASSA_PSS = 11
hLens = {'sha1': 20, 'sha256': 32}


def rsa_encrypt_plain(message, public_key):
    m = int.from_bytes(message)
    c = pow(m, public_key.e, public_key.n)
    return c.to_bytes(public_key.size_in_bytes())


def rsa_decrypt_plain(encrypted, private_key):
    e = int.from_bytes(encrypted)
    p = pow(e, private_key.d, private_key.n)
    return p.to_bytes(private_key.size_in_bytes())


def mgf1(mgfSeed, maskLen, hashFnc):
    hLen, t = hLens[hashFnc], b''
    for i in range(math.ceil(maskLen / hLen)):
        t += hashlib.new(hashFnc, mgfSeed + i.to_bytes(4)).digest()
    return t[:maskLen]


def rsa_encrypt(plaintext, pubkey, scheme=RSAES_OAEP, hashFnc='sha1', oaepLabel=b''):
    emLen = pubkey.size_in_bytes()
    hLen = hLens[hashFnc]

    if scheme == RSAES_PKCS1_v1_5:
        assert(len(plaintext) <= emLen-3)
        PS = bytearray(emLen - len(plaintext) - 3)
        for i in range(len(PS)): PS[i] = random.randrange(1, 255)
        em = b'\0\2' + PS + b'\0' + plaintext

    elif scheme == RSAES_OAEP:
        assert(len(plaintext) <= emLen -2*hLen -2)
        lHash = hashlib.new(hashFnc, oaepLabel).digest()
        PS = b'\0' * (emLen - len(plaintext) - 2*hLen - 2 );
        DB = lHash + PS + b'\1' + plaintext
        seed = os.urandom(hLen)
        dbMask = mgf1(seed, emLen-hLen-1, hashFnc)
        maskedDB = strxor(DB, dbMask)
        seedMask = mgf1(maskedDB, hLen, hashFnc)
        maskedSeed = strxor(seed, seedMask)
        em = b'\0' + maskedSeed + maskedDB

    return rsa_encrypt_plain(em, pubkey) 


def rsa_decrypt(ciphertext, privkey, hashFnc='sha1', oaepLabel=b''):
    emLen = privkey.size_in_bytes()
    if (len(ciphertext) > emLen): raise ValueError('Decrypt failed')
    em = rsa_decrypt_plain(ciphertext, privkey)

    if em[:2] == b'\0\2':
        q = em.find(b'\0', 2)
        plaintext = em[q+1:]
        return plaintext

    elif em[:1] == b'\0':        
        hLen = hLens[hashFnc]

        maskedSeed = em[1:1+hLen]
        maskedDB = em[hLen+1:]
        seedMask = mgf1(maskedDB, hLen, hashFnc)
        seed = strxor(maskedSeed, seedMask)
        dbMask = mgf1(seed, emLen-hLen-1, hashFnc)
        DB = strxor(maskedDB, dbMask)

        lHash = hashlib.new(hashFnc, oaepLabel).digest()
        if DB[:hLen] == lHash:
            q = DB.find(b'\1', hLen)
            plaintext = DB[q+1:]
            return plaintext
        elif DB[hLen] == 0:
            q = DB.find(b'\1', hLen)
            plaintext = DB[q+1:]
            return plaintext + b' (oaep label failure)'
        else: raise ValueError('Decrypt failed')

    else: raise ValueError('Decrypt failed')


def rsa_sign(message, privkey, scheme=RSASSA_PSS, hashFnc='sha1'):
    emLen = privkey.size_in_bytes()
    hLen = hLens[hashFnc]

    if scheme == RSASSA_PKCS1_v1_5:
        H = hashlib.new(hashFnc, message).digest()
        if hashFnc == 'sha1': T = binascii.unhexlify('3021300906052b0e03021a05000414') + H
        elif hashFnc == 'sha256': T = binascii.unhexlify('3031300d060960864801650304020105000420') + H
        tLen = len(T)
        PS = b'\xff' * (emLen-tLen-3)
        em = b'\0\1' + PS + b'\0' + T

    elif scheme == RSASSA_PSS:
        mHash = hashlib.new(hashFnc, message).digest()
        salt = os.urandom(hLen)
        sLen = hLen;
        Mm = b'\0\0\0\0\0\0\0\0' + mHash + salt
        H = hashlib.new(hashFnc, Mm).digest()
        PS = b'\0' * (emLen-sLen-hLen-2)
        DB = PS + b'\1' + salt
        dbMask = mgf1(H, emLen-hLen-1, hashFnc)
        maskedDB = bytearray(strxor(DB, dbMask))
        maskedDB[0] &= 0x7f
        em = maskedDB + H + b'\xbc'

    return rsa_decrypt_plain(em, privkey)


def rsa_verify(message, signature, pubkey, hashFnc='sha1'):
    emLen = pubkey.size_in_bytes()
    if (len(signature) > emLen): return False
    emm = rsa_encrypt_plain(signature, pubkey)

    if emm[:10] == b'\0\1\xff\xff\xff\xff\xff\xff\xff\xff':
        q = emm.find(b'\0', 2)
        if emm[q+1:q+16] == binascii.unhexlify('3021300906052b0e03021a05000414'):
            hashFnc = 'sha1'
            H = emm[q+16:]
        elif emm[q+1:q+20] == binascii.unhexlify(
            '3031300d060960864801650304020105000420'):
            hashFnc = 'sha256'
            H = emm[q+20:]
        else: return False
        return True if hashlib.new(hashFnc, message).digest() == H else False

    elif emm[-1:] == b'\xbc':
        hLen = hLens[hashFnc]

        maskedDB = emm[:emLen-hLen-1]
        H = emm[emLen-hLen-1:-1]
        dbMask = mgf1(H, emLen - hLen - 1, hashFnc)
        DB = strxor(maskedDB, dbMask)
        q = DB.find(b'\1')
        salt = DB[q+1:]

        mHash = hashlib.new(hashFnc, message).digest()
        Mm = b'\0\0\0\0\0\0\0\0' + mHash + salt
        return True if hashlib.new(hashFnc, Mm).digest() == H else False


# Main

# privkey = Crypto.PublicKey.RSA.generate(2048)
pem = (b'-----BEGIN RSA PRIVATE KEY-----\n'
    b'MIIEogIBAAKCAQEA4mHtauFXGkOWiuUasGosMrU+u71uJl0vL2YyaicKaxuDBzS9'
    b'vQHipgHFljypTH/It8YJQgwkiyGGF9zDjwIhHeZr239pXq7ECgC+dTcPwB1OJCkw'
    b'NT7rJQn9Q66nIjmLvyov+itPib2bRaRHVj2MulcRvqFAGFb1pQta5nNN/A4lEquM'
    b'FkxgSU4I+6vTcr8xkZ/KfnMA+f4l1IdEloeHs4qDdNqqVsPp4pKZeNUvOIHsj/j/'
    b'02VoK81jGsCmTxOKTt2uYJnr9oKOBp85LGHtNnpSk2puKYEbigr93FEAuQi3yDOn'
    b'3dlf8jOQKYvQxTzx2X7DRLbHv6yfzY4n6E/6CQIDAQABAoIBACFONU7pVSu/hYPs'
    b'vexLdTIxTnKc0CT5G6qLt19nsVWIXX1vac9yBLrV/ZBOChL/pR49wU9EGGeXEzJ/'
    b'37jdStWqeJ7OlB2CdRlgT6T7aKf5Mm2z2OxUfpAwnoqub4IOWPwobu44IK0L8K6i'
    b'bdOxyCUCufvDnyRAPZvpBkLA9FhgeMPFrvxJpabqFyIr4TFPhVacYZzlX6+ot6Xa'
    b'3Z1K0qYxjaVhVWeQaukWwkgXR0d1OBVXBPjS2DJgd6Z4PtXd4qRHyNIrtcxOS3GW'
    b'GfcpwQqzhwgo1Myf/1k+YXnVU9bMepBQLxANfw8ns4zZK3keZvz2rEk1p30cLXSG'
    b'qI6U41sCgYEA5GLCOcQr7PKot+GcKy/vjhuJeojNDFQ/SQiai322TnXW1nc0WC7x'
    b'Fcm1K2kl/zWWc6JwlKd9E2iBqHPbJa9hcSK87R+AE0GF7CRmk5NHUqSZGDpm1uWM'
    b'+edhgGoExMpsRFjmKKAPA+UWuB49xgnsUDG3HxQNcofX7syKAX02PmcCgYEA/cEp'
    b'fQiBmiU+5SpIkGQa0WwDmw02bRcyK2vBuXyRBmC2eOdtVJ+C3LHuY/05stN/9SLa'
    b'dQ+96TU3nJJE572Ier4mwLKq34aWKT+C5lKCBxNze260k4giELUJwOpoA97rgFAm'
    b'4KVq1cdp9KxzOhPjS9HWM86wojDw3Dpb3iqz3g8CgYABh6PTbTv6F1oH+UvpgiWx'
    b'pv+RwY7WEU5nN9aJLqtk9SceQqgoGxBkW/iJtOebQQmj9qeYZ1LQKXgM39HM+9LE'
    b'Rj5LvFVIS70Q6uGBBZCJvi6EWgfMUrdSCTm++XbUtqJpBstr5D6VgRhY3WL+i5x4'
    b'oQyf+atpY/2PTPFztxoA6wKBgCRtVkdcsT4vmpfLOh+AP1lQ6DOZ8fY3Hjyde3Hl'
    b'L+x6dbdlgYxkWaTU5iP0dhP1yKioGDQ1zk1sFk+jr8CUtMLqCSYgf+cWqvfA5kmq'
    b'DoB1il5txf5nzHwZgQzwmX30wlnpJ6uYE34c4lj9aI0tzbNUrCtDwJeH7wuuVQHP'
    b'n4KBAoGANpJMf8DCM6J4X6PFc7qIJL/NYofJ8UJ2B3AQG9vi+mJ2ZnrLD+r06ABP'
    b'LKPeaIq1u5UnuMLqm0XmjOzIFt+DRyQx0AGQU+GCBBN7XrUCWVtAzmZN9bbAIUOl'
    b'kxcHupJwIS4nWJcEBs5WokeiXom3/4RcVuCpreHQ+01KSsjF16k=\n'
    b'-----END RSA PRIVATE KEY-----')
privkey = Crypto.PublicKey.RSA.import_key(pem)

pubkey = privkey.publickey()
message = b'Hello World'
hash = 'sha256'
label = b''

ciphertext = rsa_encrypt_plain(message, pubkey)
print(len(ciphertext))
plaintext = rsa_decrypt_plain(ciphertext, privkey)
print(plaintext)

ciphertext = rsa_encrypt(message, pubkey, RSAES_OAEP, hash, label)
print(len(ciphertext))
plaintext = rsa_decrypt(ciphertext, privkey, hash, label)
print(plaintext)

signature = rsa_sign(message, privkey, RSASSA_PSS, hash)
print(len(signature))
ok = rsa_verify(message, signature, pubkey, hash)
print('Signature', 'OK' if ok else 'NOK')
