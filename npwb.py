#!/usr/bin/env python

# This is an experimental version, please use it with care

#
# jackjack's npw.py
# https://github.com/jackjack-jj/npw
# Released under GPLv3
#

import sys,time,os,base64,random,struct,platform
import threading
from getpass import getpass
import hashlib
from datetime import datetime
import urllib2

def randomk():
	return long(os.urandom(32).encode('hex'),16)

def sqrt_mod(a, p):
	return pow(a, (p+1)/4, p)
def verify_message_Bitcoin(address, signature, message, pureECDSASigning=False):
    networkversion=str_to_long(b58decode(address, None)) >> (8*24)
    msg=message
    if not pureECDSASigning:
        msg=Hash(format_msg_to_sign(message))

    compressed=False
    curve = curve_secp256k1
    G = generator_secp256k1
    _a,_b,_p=curve.a(),curve.b(),curve.p()

    order = G.order()
    sig = base64.b64decode(signature)
    if len(sig) != 65:
        raise Exception("vmB","Bad signature")

    hb = ord(sig[0])
    r,s = map(str_to_long,[sig[1:33],sig[33:65]])

    if hb < 27 or hb >= 35:
        raise Exception("vmB","Bad first byte")
    if hb >= 31:
        compressed = True
        hb -= 4

    recid = hb - 27
    x = (r + (recid/2) * order) % _p
    y2 = ( pow(x,3,_p) + _a*x + _b ) % _p
    yomy = sqrt_mod(y2, _p)
    if (yomy - recid) % 2 == 0:
        y=yomy
    else:
        y=_p - yomy

    R = Point(curve, x, y, order)
    e = str_to_long(msg)
    minus_e = -e % order
    inv_r = inverse_mod(r,order)
    Q = inv_r * ( R*s + G*minus_e )

    public_key = Public_key(G, Q, compressed)
    addr = public_key_to_bc_address(public_key.ser(), networkversion)
    if address != addr:
        raise Exception("vmB","Bad address. Signing: %s, received: %s"%(addr,address))


def sign_message(secret, message, pureECDSASigning=False):
	if len(secret) == 32:
		pkey = EC_KEY(str_to_long(secret))
		compressed = False
	elif len(secret) == 33:
		pkey = EC_KEY(str_to_long(secret[:-1]))
		secret=secret[:-1]
		compressed = True
	else:
		raise Exception("sm","Bad private key size (%d)"%len(secret))

	msg=message
	if not pureECDSASigning:
		msg=Hash(format_msg_to_sign(message))

	eckey           = EC_KEY(str_to_long(secret), compressed)
	private_key     = eckey.privkey
	public_key      = eckey.pubkey
	addr            = public_key_to_bc_address(GetPubKey(eckey,eckey.pubkey.compressed))

	sig = private_key.sign(msg, randomk())
	if not public_key.verify(msg, sig):
		raise Exception("sm","Problem signing message")
	return [sig,addr,compressed,public_key]


def sign_message_Bitcoin(secret, msg, pureECDSASigning=False):
	sig,addr,compressed,public_key=sign_message(secret, msg, pureECDSASigning)

	for i in range(4):
		hb=27+i
		if compressed:
			hb+=4
		sign=base64.b64encode(chr(hb)+sig.ser())
		try:
			verify_message_Bitcoin(addr, sign, msg, pureECDSASigning)
			return {'address':addr, 'b64-signature':sign, 'signature':chr(hb)+sig.ser(), 'message':msg}
		except Exception as e:
#			print e.args
			pass

	raise Exception("smB","Unable to construct recoverable key")

def FormatText(t, sigctx, verbose=False):   #sigctx: False=what is displayed, True=what is signed
	r=''
	te=t.split('\n')
	for l in te:
		while len(l) and l[len(l)-1] in [' ', '\t', chr(9)]:
			l=l[:-1]
		if not len(l) or l[len(l)-1]!='\r':
			l+='\r'
		if not sigctx:
			if len(l) and l[0]=='-':
				l='- '+l[1:]
		r+=l+'\n'
	r=r[:-2]

	global FTVerbose
	if FTVerbose:
		print '  -- Sent:      '+t.encode('hex')
		if sigctx:
			print '  -- Signed:    '+r.encode('hex')
		else:
			print '  -- Displayed: '+r.encode('hex')

	return r


def crc24(m):
	INIT = 0xB704CE
	POLY = 0x1864CFB
	crc = INIT
	r = ''
	for o in m:
		o=ord(o)
		crc ^= (o << 16)
		for i in xrange(8):
			crc <<= 1
			if crc & 0x1000000:
				crc ^= POLY
	for i in range(3):
		r += chr( ( crc & (0xff<<(8*i))) >> (8*i) )
	return r

def chunks(t, n):
	return [t[i:i+n] for i in range(0, len(t), n)]

def ASCIIArmory(block, name):
	r='-----BEGIN '+name+'-----\r\n'
	r+='\r\n'.join(chunks(base64.b64encode(block), 64))+'\r\n='
	r+=base64.b64encode(crc24(block))+'\r\n'
	r+='-----END '+name+'-----'
	return r


#==============================================

def verifySignature(addr, b64sig, msg):
	return verify_message_Bitcoin(addr, b64sig, FormatText(msg, True))



import os
import time
import traceback
from datetime import datetime
from bsddb.db import *

def hash_160(public_key):
 	md = hashlib.new('ripemd160')
	md.update(hashlib.sha256(public_key).digest())
	return md.digest()

def public_key_to_bc_address(public_key, v=None):
	if v==None:
		v=addrtype
	h160 = hash_160(public_key)
	return hash_160_to_bc_address(h160, v)

def hash_160_to_bc_address(h160, v=None):
	if v==None:
		v=addrtype
	vh160 = chr(v) + h160
	h = Hash(vh160)
	addr = vh160 + h[0:4]
	return b58encode(addr)

def bc_address_to_hash_160(addr):
	bytes = b58decode(addr, 25)
	return bytes[1:21]

__b58chars = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
__b58base = len(__b58chars)

def b58encode(v):
	""" encode v, which is a string of bytes, to base58.
	"""

	long_value = 0L
	for (i, c) in enumerate(v[::-1]):
		long_value += (256**i) * ord(c)

	result = ''
	while long_value >= __b58base:
		div, mod = divmod(long_value, __b58base)
		result = __b58chars[mod] + result
		long_value = div
	result = __b58chars[long_value] + result

	# Bitcoin does a little leading-zero-compression:
	# leading 0-bytes in the input become leading-1s
	nPad = 0
	for c in v:
		if c == '\0': nPad += 1
		else: break

	return (__b58chars[0]*nPad) + result

def b58decode(v, length):
	""" decode v into a string of len bytes
	"""
	long_value = 0L
	for (i, c) in enumerate(v[::-1]):
		long_value += __b58chars.find(c) * (__b58base**i)

	result = ''
	while long_value >= 256:
		div, mod = divmod(long_value, 256)
		result = chr(mod) + result
		long_value = div
	result = chr(long_value) + result

	nPad = 0
	for c in v:
		if c == __b58chars[0]: nPad += 1
		else: break

	result = chr(0)*nPad + result
	if length is not None and len(result) != length:
		return None

	return result

# end of bitcointools base58 implementation

# address handling code

def long_hex(bytes):
	return bytes.encode('hex_codec')

def Hash(data):
	return hashlib.sha256(hashlib.sha256(data).digest()).digest()

def EncodeBase58Check(secret):
	hash = Hash(secret)
	return b58encode(secret + hash[0:4])

def DecodeBase58Check(sec):
	vchRet = b58decode(sec, None)
	secret = vchRet[0:-4]
	csum = vchRet[-4:]
	hash = Hash(secret)
	cs32 = hash[0:4]
	if cs32 != csum:
		return None
	else:
		return secret

def str_to_long(b):
	res = 0
	pos = 1
	for a in reversed(b):
		res += ord(a) * pos
		pos *= 256
	return res

def PrivKeyToSecret(privkey):
	if len(privkey) == 279:
		return privkey[9:9+32]
	else:
		return privkey[8:8+32]

def SecretToASecret(secret, compressed=False):
	prefix = chr((addrtype+128)&255)
	if addrtype==48:  #assuming Litecoin
		prefix = chr(128)
	vchIn = prefix + secret
	if compressed: vchIn += '\01'
	return EncodeBase58Check(vchIn)

def ASecretToSecret(sec):
	vch = DecodeBase58Check(sec)
	if not vch:
		return False
	if vch[0] != chr((addrtype+128)&255):
		print 'Warning: adress prefix seems bad (%d vs %d)'%(ord(vch[0]), (addrtype+128)&255)
	return vch[1:]

def regenerate_key(sec):
	b = ASecretToSecret(sec)
	if not b:
		return False
	b = b[0:32]
	secret = int('0x' + b.encode('hex'), 16)
	return EC_KEY(secret)

def GetPubKey(pkey, compressed=False):
	return i2o_ECPublicKey(pkey, compressed)

def GetPrivKey(pkey, compressed=False):
	return i2d_ECPrivateKey(pkey, compressed)

def GetSecret(pkey):
	return ('%064x' % pkey.secret).decode('hex')

def is_compressed(sec):
	b = ASecretToSecret(sec)
	return len(b) == 33

# bitcointools wallet.dat handling code

def create_env(db_dir):
	db_env = DBEnv(0)
	r = db_env.open(db_dir, (DB_CREATE|DB_INIT_LOCK|DB_INIT_LOG|DB_INIT_MPOOL|DB_INIT_TXN|DB_THREAD|DB_RECOVER))
	return db_env

def parse_CAddress(vds):
	d = {'ip':'0.0.0.0','port':0,'nTime': 0}
	try:
		d['nVersion'] = vds.read_int32()
		d['nTime'] = vds.read_uint32()
		d['nServices'] = vds.read_uint64()
		d['pchReserved'] = vds.read_bytes(12)
		d['ip'] = socket.inet_ntoa(vds.read_bytes(4))
		d['port'] = vds.read_uint16()
	except:
		pass
	return d

def deserialize_CAddress(d):
	return d['ip']+":"+str(d['port'])

def parse_BlockLocator(vds):
	d = { 'hashes' : [] }
	nHashes = vds.read_compact_size()
	for i in xrange(nHashes):
		d['hashes'].append(vds.read_bytes(32))
		return d

def deserialize_BlockLocator(d):
  result = "Block Locator top: "+d['hashes'][0][::-1].encode('hex_codec')
  return result

def parse_setting(setting, vds):
	if setting[0] == "f":	# flag (boolean) settings
		return str(vds.read_boolean())
	elif setting[0:4] == "addr": # CAddress
		d = parse_CAddress(vds)
		return deserialize_CAddress(d)
	elif setting == "nTransactionFee":
		return vds.read_int64()
	elif setting == "nLimitProcessors":
		return vds.read_int32()
	return 'unknown setting'

class SerializationError(Exception):
	""" Thrown when there's a problem deserializing or serializing """



class BCDataStream(object):
	def __init__(self):
		self.input = None
		self.read_cursor = 0

	def clear(self):
		self.input = None
		self.read_cursor = 0

	def write(self, bytes):	# Initialize with string of bytes
		if self.input is None:
			self.input = bytes
		else:
			self.input += bytes

	def map_file(self, file, start):	# Initialize with bytes from file
		self.input = mmap.mmap(file.fileno(), 0, access=mmap.ACCESS_READ)
		self.read_cursor = start
	def seek_file(self, position):
		self.read_cursor = position
	def close_file(self):
		self.input.close()

	def read_string(self):
		# Strings are encoded depending on length:
		# 0 to 252 :	1-byte-length followed by bytes (if any)
		# 253 to 65,535 : byte'253' 2-byte-length followed by bytes
		# 65,536 to 4,294,967,295 : byte '254' 4-byte-length followed by bytes
		# ... and the Bitcoin client is coded to understand:
		# greater than 4,294,967,295 : byte '255' 8-byte-length followed by bytes of string
		# ... but I don't think it actually handles any strings that big.
		if self.input is None:
			raise SerializationError("call write(bytes) before trying to deserialize")

		try:
			length = self.read_compact_size()
		except IndexError:
			raise SerializationError("attempt to read past end of buffer")

		return self.read_bytes(length)

	def write_string(self, string):
		# Length-encoded as with read-string
		self.write_compact_size(len(string))
		self.write(string)

	def read_bytes(self, length):
		try:
			result = self.input[self.read_cursor:self.read_cursor+length]
			self.read_cursor += length
			return result
		except IndexError:
			raise SerializationError("attempt to read past end of buffer")

		return ''

	def read_boolean(self): return self.read_bytes(1)[0] != chr(0)
	def read_int16(self): return self._read_num('<h')
	def read_uint16(self): return self._read_num('<H')
	def read_int32(self): return self._read_num('<i')
	def read_uint32(self): return self._read_num('<I')
	def read_int64(self): return self._read_num('<q')
	def read_uint64(self): return self._read_num('<Q')

	def write_boolean(self, val): return self.write(chr(bool_to_int(val)))
	def write_int16(self, val): return self._write_num('<h', val)
	def write_uint16(self, val): return self._write_num('<H', val)
	def write_int32(self, val): return self._write_num('<i', val)
	def write_uint32(self, val): return self._write_num('<I', val)
	def write_int64(self, val): return self._write_num('<q', val)
	def write_uint64(self, val): return self._write_num('<Q', val)

	def read_compact_size(self):
		size = ord(self.input[self.read_cursor])
		self.read_cursor += 1
		if size == 253:
			size = self._read_num('<H')
		elif size == 254:
			size = self._read_num('<I')
		elif size == 255:
			size = self._read_num('<Q')
		return size

	def write_compact_size(self, size):
		if size < 0:
			raise SerializationError("attempt to write size < 0")
		elif size < 253:
			 self.write(chr(size))
		elif size < 2**16:
			self.write('\xfd')
			self._write_num('<H', size)
		elif size < 2**32:
			self.write('\xfe')
			self._write_num('<I', size)
		elif size < 2**64:
			self.write('\xff')
			self._write_num('<Q', size)

	def _read_num(self, format):
		(i,) = struct.unpack_from(format, self.input, self.read_cursor)
		self.read_cursor += struct.calcsize(format)
		return i

	def _write_num(self, format, num):
		s = struct.pack(format, num)
		self.write(s)



def random_string(l, alph="0123456789abcdef"):
	r=""
	la=len(alph)
	for i in range(l):
		r+=alph[int(la*(random.random()))]
	return r

def iais(a):
	if a>= 2:
		return 's'
	else:
		return ''

def aversions(n):
	return 'Version '+str(n)

###################################
# pywallet crypter implementation #
###################################

crypter = None

try:
	from Crypto.Cipher import AES
	crypter = 'pycrypto'
except:
	pass

class Crypter_pycrypto( object ):
	def SetKeyFromPassphrase(self, vKeyData, vSalt, nDerivIterations, nDerivationMethod):
		if nDerivationMethod != 0:
			return 0
		data = vKeyData + vSalt
		for i in xrange(nDerivIterations):
			data = hashlib.sha512(data).digest()
		self.SetKey(data[0:32])
		self.SetIV(data[32:32+16])
		return len(data)

	def SetKey(self, key):
		self.chKey = key

	def SetIV(self, iv):
		self.chIV = iv[0:16]

	def Encrypt(self, data):
		return AES.new(self.chKey,AES.MODE_CBC,self.chIV).encrypt(data)[0:32]

	def Decrypt(self, data):
		return AES.new(self.chKey,AES.MODE_CBC,self.chIV).decrypt(data)[0:32]

try:
	if not crypter:
		import ctypes
		import ctypes.util
		module_ssl = ctypes.cdll.LoadLibrary (ctypes.util.find_library ('ssl') or 'libeay32')
		crypter = 'ssl'
except:
	pass

class Crypter_ssl(object):
	def __init__(self):
		self.chKey = ctypes.create_string_buffer (32)
		self.chIV = ctypes.create_string_buffer (16)

	def SetKeyFromPassphrase(self, vKeyData, vSalt, nDerivIterations, nDerivationMethod):
		if nDerivationMethod != 0:
			return 0
		strKeyData = ctypes.create_string_buffer (vKeyData)
		chSalt = ctypes.create_string_buffer (vSalt)
		return module_ssl.EVP_BytesToKey(module_ssl.EVP_aes_256_cbc(), module_ssl.EVP_sha512(), chSalt, strKeyData,
			len(vKeyData), nDerivIterations, ctypes.byref(self.chKey), ctypes.byref(self.chIV))

	def SetKey(self, key):
		self.chKey = ctypes.create_string_buffer(key)

	def SetIV(self, iv):
		self.chIV = ctypes.create_string_buffer(iv)

	def Encrypt(self, data):
		buf = ctypes.create_string_buffer(len(data) + 16)
		written = ctypes.c_int(0)
		final = ctypes.c_int(0)
		ctx = module_ssl.EVP_CIPHER_CTX_new()
		module_ssl.EVP_CIPHER_CTX_init(ctx)
		module_ssl.EVP_EncryptInit_ex(ctx, module_ssl.EVP_aes_256_cbc(), None, self.chKey, self.chIV)
		module_ssl.EVP_EncryptUpdate(ctx, buf, ctypes.byref(written), data, len(data))
		output = buf.raw[:written.value]
		module_ssl.EVP_EncryptFinal_ex(ctx, buf, ctypes.byref(final))
		output += buf.raw[:final.value]
		return output

	def Decrypt(self, data):
		buf = ctypes.create_string_buffer(len(data) + 16)
		written = ctypes.c_int(0)
		final = ctypes.c_int(0)
		ctx = module_ssl.EVP_CIPHER_CTX_new()
		module_ssl.EVP_CIPHER_CTX_init(ctx)
		module_ssl.EVP_DecryptInit_ex(ctx, module_ssl.EVP_aes_256_cbc(), None, self.chKey, self.chIV)
		module_ssl.EVP_DecryptUpdate(ctx, buf, ctypes.byref(written), data, len(data))
		output = buf.raw[:written.value]
		module_ssl.EVP_DecryptFinal_ex(ctx, buf, ctypes.byref(final))
		output += buf.raw[:final.value]
		return output

class Crypter_pure(object):
	def __init__(self):
		self.m = AESModeOfOperation()
		self.cbc = self.m.modeOfOperation["CBC"]
		self.sz = self.m.aes.keySize["SIZE_256"]

	def SetKeyFromPassphrase(self, vKeyData, vSalt, nDerivIterations, nDerivationMethod):
		if nDerivationMethod != 0:
			return 0
		data = vKeyData + vSalt
		for i in xrange(nDerivIterations):
			data = hashlib.sha512(data).digest()
		self.SetKey(data[0:32])
		self.SetIV(data[32:32+16])
		return len(data)

	def SetKey(self, key):
		self.chKey = [ord(i) for i in key]

	def SetIV(self, iv):
		self.chIV = [ord(i) for i in iv]

	def Encrypt(self, data):
		mode, size, cypher = self.m.encrypt(data, self.cbc, self.chKey, self.sz, self.chIV)
		return ''.join(map(chr, cypher))

	def Decrypt(self, data):
		chData = [ord(i) for i in data]
		return self.m.decrypt(chData, self.sz, self.cbc, self.chKey, self.sz, self.chIV)

if crypter == 'pycrypto':
	crypter = Crypter_pycrypto()
#	print "Crypter: pycrypto"
elif crypter == 'ssl':
	crypter = Crypter_ssl()
#	print "Crypter: ssl"
else:
	crypter = Crypter_pure()
#	print "Crypter: pure"
	logging.warning("pycrypto or libssl not found, decryption may be slow")

##########################################
# end of pywallet crypter implementation #
##########################################

def npw_update_wallet(db, types, datas, paramsAreLists=False):
	"""Write a single item to the wallet.
	db must be open with writable=True.
	type and data are the type code and data dictionary as parse_wallet would
	give to item_callback.
	data's __key__, __value__ and __type__ are ignored; only the primary data
	fields are used.
	"""

	if not paramsAreLists:
		types=[types]
		datas=[datas]

	if len(types)!=len(datas):
		raise Exception("UpdateWallet: sizes are different")

	for it,type in enumerate(types):
		data=datas[it]

		d = data
		kds = BCDataStream()
		vds = BCDataStream()

		# Write the type code to the key
		kds.write_string(type)
		vds.write("")						 # Ensure there is something

		try:
			if type == "tx":
	#			raise NotImplementedError("Writing items of type 'tx'")
				kds.write(d['txi'][6:].decode('hex_codec'))
				vds.write(d['txv'].decode('hex_codec'))
			elif type == "name":
				kds.write_string(d['hash'])
				vds.write_string(d['name'])
			elif type == "version":
				vds.write_uint32(d['version'])
			elif type == "minversion":
				vds.write_uint32(d['minversion'])
			elif type == "setting":
				raise NotImplementedError("Writing items of type 'setting'")
				kds.write_string(d['setting'])
				#d['value'] = parse_setting(d['setting'], vds)
			elif type == "key":
				kds.write_string(d['public_key'])
				vds.write_string(d['private_key'])
			elif type == "wkey":
				kds.write_string(d['public_key'])
				vds.write_string(d['private_key'])
				vds.write_int64(d['created'])
				vds.write_int64(d['expires'])
				vds.write_string(d['comment'])
			elif type == "defaultkey":
				vds.write_string(d['key'])
			elif type == "pool":
				kds.write_int64(d['n'])
				vds.write_int32(d['nVersion'])
				vds.write_int64(d['nTime'])
				vds.write_string(d['public_key'])
			elif type == "acc":
				kds.write_string(d['account'])
				vds.write_int32(d['nVersion'])
				vds.write_string(d['public_key'])
			elif type == "acentry":
				kds.write_string(d['account'])
				kds.write_uint64(d['n'])
				vds.write_int32(d['nVersion'])
				vds.write_int64(d['nCreditDebit'])
				vds.write_int64(d['nTime'])
				vds.write_string(d['otherAccount'])
				vds.write_string(d['comment'])
			elif type == "bestblock":
				vds.write_int32(d['nVersion'])
				vds.write_compact_size(len(d['hashes']))
				for h in d['hashes']:
					vds.write(h)
			elif type == "ckey":
				kds.write_string(d['public_key'])
				vds.write_string(d['encrypted_private_key'])
			elif type == "mkey":
				kds.write_uint32(d['nID'])
				vds.write_string(d['encrypted_key'])
				vds.write_string(d['salt'])
				vds.write_uint32(d['nDerivationMethod'])
				vds.write_uint32(d['nDerivationIterations'])
				vds.write_string(d['otherParams'])

			else:
				print "Unknown key type: "+type

			# Write the key/value pair to the database
			db.put(kds.input, vds.input)

		except Exception, e:
			print("ERROR writing to wallet.dat, type %s"%type)
			print("data dictionary: %r"%data)
			traceback.print_exc()

def is_compressed(sec):
	b = ASecretToSecret(sec)
	return len(b) == 33


def npw_import_csv_keys_to_wallet(filename, db, json_db, passphrase, fct_callback=False, nbremax=9999999):
#	global global_merging_message
	if filename[0]=="\x00":    #yeah, dirty workaround
		content=filename[1:]
	else:
		filen = open(filename, "r")
		content = filen.read()
		filen.close()

	content=content.split('\n')
	content=content[:min(nbremax, len(content))]
	lencontent=len(content)
	for i in range(lencontent):
	  c=content[i]
	  if fct_callback:
	    fct_callback(i, lencontent)
#	  global_merging_message = ["Merging: "+str(round(100.0*(i+1)/lencontent,1))+"%" for j in range(2)]
	  if ';' in c and len(c)>0 and c[0]!="#":
		cs=c.split(';')
		sec,label=cs[0:2]
		v=0
		if len(cs)>2:
			v=int(cs[2])
		reserve=False
		if label=="#Reserve":
			reserve=True
		keyishex=None
		if abs(len(sec)-65)==1:
			keyishex=True
		npw_importprivkey(db, json_db, sec, label, reserve, 'keyishex', False, 0, passphrase)

#	global_merging_message = ["Merging done.", ""]

	return True

def npw_importprivkey(db, json_db, sec, label, reserve, keyishex, verbose=True, addrv=0, passphrase=''):
	if len(sec) == 64:
		pkey = EC_KEY(str_to_long(sec.decode('hex')))
		compressed = False
	elif len(sec) == 66:
		pkey = EC_KEY(str_to_long(sec[:-2].decode('hex')))
		compressed = True
	else:
		pkey = regenerate_key(sec)
		compressed = is_compressed(sec)

	if not pkey:
		print "Bad private key (length:"+str(len(sec))+")"
		return False

	secret = GetSecret(pkey)
	private_key = GetPrivKey(pkey, compressed)
	public_key = GetPubKey(pkey, compressed)
	addr = public_key_to_bc_address(public_key, addrv)

	if verbose:
		print "Address (%s): %s"%(aversions(addrv), addr)
		print "Privkey (%s): %s"%(aversions(addrv), SecretToASecret(secret, compressed))
		print "Hexprivkey: %s"%(secret.encode('hex'))
		print "Hash160: %s"%(bc_address_to_hash_160(addr).encode('hex'))
		if not compressed:
			print "Pubkey: 04%.64x%.64x"%(pkey.pubkey.point.x(), pkey.pubkey.point.y())
		else:
			print "Pubkey: 0%d%.64x"%(2+(pkey.pubkey.point.y()&1), pkey.pubkey.point.x())
		if int(secret.encode('hex'), 16)>_r:
			print 'Beware, 0x%s is equivalent to 0x%.33x</b>'%(secret.encode('hex'), int(secret.encode('hex'), 16)-_r)



	global crypter
	crypted = False
	if 'mkey' in json_db.keys() and 'salt' in json_db['mkey']:
		crypted = True
	if crypted:
		if passphrase:
			cry_master = json_db['mkey']['encrypted_key'].decode('hex')
			cry_salt   = json_db['mkey']['salt'].decode('hex')
			cry_rounds = json_db['mkey']['nDerivationIterations']
			cry_method = json_db['mkey']['nDerivationMethod']

			crypter.SetKeyFromPassphrase(passphrase, cry_salt, cry_rounds, cry_method)
			masterkey = crypter.Decrypt(cry_master)
			crypter.SetKey(masterkey)
			crypter.SetIV(Hash(public_key))
			e = crypter.Encrypt(secret)
			ck_epk=e

			npw_update_wallet(db, 'ckey', { 'public_key' : public_key, 'encrypted_private_key' : ck_epk })
	else:
		npw_update_wallet(db, 'key', { 'public_key' : public_key, 'private_key' : private_key })

	if not reserve:
		npw_update_wallet(db, 'name', { 'hash' : addr, 'name' : label })


	return True

def parse_wallet(db, item_callback):
	kds = BCDataStream()
	vds = BCDataStream()

	def parse_TxIn(vds):
		d = {}
		d['prevout_hash'] = vds.read_bytes(32).encode('hex')
		d['prevout_n'] = vds.read_uint32()
		d['scriptSig'] = vds.read_bytes(vds.read_compact_size()).encode('hex')
		d['sequence'] = vds.read_uint32()
		return d

	def parse_TxOut(vds):
		d = {}
		d['value'] = vds.read_int64()/1e8
		d['scriptPubKey'] = vds.read_bytes(vds.read_compact_size()).encode('hex')
		return d

	for (key, value) in db.items():
		d = { }

		kds.clear(); kds.write(key)
		vds.clear(); vds.write(value)

		type = kds.read_string()

		d["__key__"] = key
		d["__value__"] = value
		d["__type__"] = type

		try:
			if type == "tx":
				d["tx_id"] = inversetxid(kds.read_bytes(32).encode('hex_codec'))
				start = vds.read_cursor
				d['version'] = vds.read_int32()
				n_vin = vds.read_compact_size()
				d['txIn'] = []
				for i in xrange(n_vin):
					d['txIn'].append(parse_TxIn(vds))
				n_vout = vds.read_compact_size()
				d['txOut'] = []
				for i in xrange(n_vout):
					d['txOut'].append(parse_TxOut(vds))
				d['lockTime'] = vds.read_uint32()
				d['tx'] = vds.input[start:vds.read_cursor].encode('hex_codec')
				d['txv'] = value.encode('hex_codec')
				d['txk'] = key.encode('hex_codec')
			elif type == "name":
				d['hash'] = kds.read_string()
				d['name'] = vds.read_string()
			elif type == "version":
				d['version'] = vds.read_uint32()
			elif type == "minversion":
				d['minversion'] = vds.read_uint32()
			elif type == "setting":
				d['setting'] = kds.read_string()
				d['value'] = parse_setting(d['setting'], vds)
			elif type == "key":
				d['public_key'] = kds.read_bytes(kds.read_compact_size())
				d['private_key'] = vds.read_bytes(vds.read_compact_size())
			elif type == "wkey":
				d['public_key'] = kds.read_bytes(kds.read_compact_size())
				d['private_key'] = vds.read_bytes(vds.read_compact_size())
				d['created'] = vds.read_int64()
				d['expires'] = vds.read_int64()
				d['comment'] = vds.read_string()
			elif type == "defaultkey":
				d['key'] = vds.read_bytes(vds.read_compact_size())
			elif type == "pool":
				d['n'] = kds.read_int64()
				d['nVersion'] = vds.read_int32()
				d['nTime'] = vds.read_int64()
				d['public_key'] = vds.read_bytes(vds.read_compact_size())
			elif type == "acc":
				d['account'] = kds.read_string()
				d['nVersion'] = vds.read_int32()
				d['public_key'] = vds.read_bytes(vds.read_compact_size())
			elif type == "acentry":
				d['account'] = kds.read_string()
				d['n'] = kds.read_uint64()
				d['nVersion'] = vds.read_int32()
				d['nCreditDebit'] = vds.read_int64()
				d['nTime'] = vds.read_int64()
				d['otherAccount'] = vds.read_string()
				d['comment'] = vds.read_string()
			elif type == "bestblock":
				d['nVersion'] = vds.read_int32()
				d.update(parse_BlockLocator(vds))
			elif type == "ckey":
				d['public_key'] = kds.read_bytes(kds.read_compact_size())
				d['encrypted_private_key'] = vds.read_bytes(vds.read_compact_size())
			elif type == "mkey":
				d['nID'] = kds.read_uint32()
				d['encrypted_key'] = vds.read_string()
				d['salt'] = vds.read_string()
				d['nDerivationMethod'] = vds.read_uint32()
				d['nDerivationIterations'] = vds.read_uint32()
				d['otherParams'] = vds.read_string()
			item_callback(type, d)

		except Exception, e:
			traceback.print_exc()
			print("ERROR parsing wallet.dat, type %s" % type)
			print("key data: %s"%key)
			print("key data in hex: %s"%key.encode('hex_codec'))
			print("value data in hex: %s"%value.encode('hex_codec'))
			sys.exit(1)

def create_env(db_dir,log=False):
	db_env = DBEnv(0)
	print db_dir
	flags=(DB_CREATE|DB_INIT_LOCK|DB_INIT_MPOOL|DB_INIT_TXN|DB_THREAD|DB_RECOVER)
	if log:
		flags|=DB_INIT_LOG
#	r = db_env.open(db_dir, (DB_CREATE|DB_INIT_LOCK|DB_INIT_LOG|DB_INIT_MPOOL|DB_INIT_TXN|DB_THREAD|DB_RECOVER))
	r = db_env.open(db_dir, flags)
#	print 'pre sleep', db_env
#	print dir(db_env)
#	time.sleep(15)
#	print 'post sleep'
	return db_env

def npw_open_wallet(path, writable=False):
	walletdir,walletfile=os.path.split(path)

	db = DB()
	if writable:
		DB_TYPEOPEN = DB_CREATE
	else:
		DB_TYPEOPEN = DB_RDONLY
	flags = DB_THREAD | DB_TYPEOPEN
	try:
		r = db.open(path, "main", DB_BTREE, flags)
	except DBError:
		r = True

	if r is not None:
		traceback.print_exc()
		print "Couldn't open '%s'. Try quitting Bitcoin and running this again."%path
		sys.exit(1)

	return db


def npw_read_wallet(walletpath, passphrase='', addrv=0):
	crypted=False

	db = npw_open_wallet(walletpath)

	json_db={}
	json_db['keys'] = []
	json_db['pool'] = []
	json_db['tx'] = []
	json_db['names'] = {}
	json_db['ckey'] = []
	json_db['mkey'] = {}

	def item_callback(type, d):
		if type == "tx":
			json_db['tx'].append({"tx_id" : d['tx_id'], "txin" : d['txIn'], "txout" : d['txOut'], "tx_v" : d['txv'], "tx_k" : d['txk']})

		elif type == "name":
			json_db['names'][d['hash']] = d['name']

		elif type == "version":
			json_db['version'] = d['version']

		elif type == "minversion":
			json_db['minversion'] = d['minversion']

		elif type == "setting":
			if not json_db.has_key('settings'): json_db['settings'] = {}
			json_db["settings"][d['setting']] = d['value']

		elif type == "defaultkey":
			json_db['defaultkey'] = public_key_to_bc_address(d['key'], addrv)

		elif type == "key":
			addr = public_key_to_bc_address(d['public_key'], addrv)
			compressed = d['public_key'][0] != '\04'
			sec = SecretToASecret(PrivKeyToSecret(d['private_key']), compressed)
			hexsec = ASecretToSecret(sec).encode('hex')[:64]
			json_db['keys'].append({'addr' : addr, 'sec' : sec, 'hexsec' : hexsec, 'secret' : hexsec, 'pubkey':d['public_key'].encode('hex'), 'compressed':compressed, 'private':d['private_key'].encode('hex')})

		elif type == "wkey":
			if not json_db.has_key('wkey'): json_db['wkey'] = []
			json_db['wkey']['created'] = d['created']

		elif type == "pool":
			"""	d['n'] = kds.read_int64()
				d['nVersion'] = vds.read_int32()
				d['nTime'] = vds.read_int64()
				d['public_key'] = vds.read_bytes(vds.read_compact_size())"""
			try:
				json_db['pool'].append( {'n': d['n'], 'addr': public_key_to_bc_address(d['public_key'], addrv), 'addr2': public_key_to_bc_address(d['public_key'].decode('hex'), addrv), 'addr3': public_key_to_bc_address(d['public_key'].encode('hex'), addrv), 'nTime' : d['nTime'], 'nVersion' : d['nVersion'], 'public_key_hex' : d['public_key'] } )
			except:
				json_db['pool'].append( {'n': d['n'], 'addr': public_key_to_bc_address(d['public_key'], addrv), 'nTime' : d['nTime'], 'nVersion' : d['nVersion'], 'public_key_hex' : d['public_key'].encode('hex') } )

		elif type == "acc":
			json_db['acc'] = d['account']
			print("Account %s (current key: %s)"%(d['account'], public_key_to_bc_address(d['public_key'], addrv)))

		elif type == "acentry":
			json_db['acentry'] = (d['account'], d['nCreditDebit'], d['otherAccount'], time.ctime(d['nTime']), d['n'], d['comment'])

		elif type == "bestblock":
			json_db['bestblock'] = d['hashes'][0][::-1].encode('hex_codec')

		elif type == "ckey":
			crypted=True
			compressed = d['public_key'][0] != '\04'
			json_db['keys'].append({ 'pubkey': d['public_key'].encode('hex'),'addr': public_key_to_bc_address(d['public_key'], addrv), 'encrypted_privkey':  d['encrypted_private_key'].encode('hex_codec'), 'compressed':compressed})

		elif type == "mkey":
			json_db['mkey']['nID'] = d['nID']
			json_db['mkey']['encrypted_key'] = d['encrypted_key'].encode('hex_codec')
			json_db['mkey']['salt'] = d['salt'].encode('hex_codec')
			json_db['mkey']['nDerivationMethod'] = d['nDerivationMethod']
			json_db['mkey']['nDerivationIterations'] = d['nDerivationIterations']
			json_db['mkey']['otherParams'] = d['otherParams']

			if passphrase:
				res = crypter.SetKeyFromPassphrase(passphrase, d['salt'], d['nDerivationIterations'], d['nDerivationMethod'])
				if res == 0:
					print "Unsupported derivation method"
					sys.exit(1)
				masterkey = crypter.Decrypt(d['encrypted_key'])
				crypter.SetKey(masterkey)

		else:
			json_db[type] = 'unsupported'
			print "Wallet data not recognized: "+str(d)

	list_of_reserve_not_in_pool=[]
	parse_wallet(db, item_callback)

	nkeys = len(json_db['keys'])
	i = 0
	for k in json_db['keys']:
		i+=1
		addr = k['addr']
		if False:#include_balance:
#			print("%3d/%d  %s  %s" % (i, nkeys, k["addr"], k["balance"]))
			k["balance"] = balance(balance_site, k["addr"])
#			print("  %s" % (i, nkeys, k["addr"], k["balance"]))

		if addr in json_db['names'].keys():
			k["label"] = json_db['names'][addr]
			k["reserve"] = 0
		else:
			k["reserve"] = 1
			list_of_reserve_not_in_pool.append(k['pubkey'])


	def rnip_callback(a):
		list_of_reserve_not_in_pool.remove(a['public_key_hex'])

	db.close()#remove()

	crypted = 'salt' in json_db['mkey']
	ppcorrect = True

	if not crypted:
#		print "The wallet is not encrypted"
		pass
	elif crypted and passphrase=='':
#		print "The wallet is encrypted but no passphrase is used"
		ppcorrect = False
		pass
	elif crypted and passphrase!='':
		check = True
		for k in json_db['keys']:
		  if 'encrypted_privkey' in k:
			ckey = k['encrypted_privkey'].decode('hex')
			public_key = k['pubkey'].decode('hex')
			crypter.SetIV(Hash(public_key))
			secret = crypter.Decrypt(ckey)
			compressed = public_key[0] != '\04'


			if check:
				check = False
				pkey = EC_KEY(int('0x' + secret.encode('hex'), 16))
				if public_key != GetPubKey(pkey, compressed):
#					print "The wallet is encrypted and the passphrase is incorrect"
					ppcorrect=False
					break

			sec = SecretToASecret(secret, compressed)
			k['sec'] = sec
			k['hexsec'] = secret[:32].encode('hex')
			k['secret'] = secret.encode('hex')
			k['compressed'] = compressed
#			del(k['ckey'])
#			del(k['secret'])
#			del(k['pubkey'])
		if ppcorrect:
#			print "The wallet is encrypted and the passphrase is correct"
			pass

	for k in json_db['keys']:
		if k['compressed'] and 'secret' in k:
			k['secret']+="01"


	return {'wallet':json_db,'crypted':crypted,'goodpp':ppcorrect}

def npw_export_all_keys(db, keys, filename):
	txt=";".join(keys)+"\n"
	for i in db['keys']:
	  try:
		if 'label' not in i:
			i['label']='#Reserve'
		t=";".join([str(i[k]) for k in keys])
		txt+=t+"\n"
	  except Exception as e:
		print e.args
		return False

	try:
		myFile = open(filename, 'w')
		myFile.write(txt)
		myFile.close()
		return True
	except Exception as e:
		print e.args
		return False

def search_patterns_on_disk(device, size, inc, patternlist, dw, app):   # inc must be higher than 1k
	def displayWrite(x):
		dw(x+'\n')
	try:
		otype=os.O_RDONLY|os.O_BINARY
	except:
		otype=os.O_RDONLY
	try:
		fd = os.open(device, otype)
	except Exception as e:
		displayWrite("Can't open %s, check the path or try as root"%device)
		displayWrite("  Error:", e.args)
		exit(0)

	i = 0
	data=''

	tzero=time.time()
	sizetokeep=0
	BlocksToInspect=dict(map(lambda x:[x,[]], patternlist))
	syst=systype()
	lendataloaded=None
	writeProgressEvery=100*Mo
	while lendataloaded!=0 or lendataloaded==None:
		if int(i/writeProgressEvery)!=int((i+inc)/writeProgressEvery):
			displayWrite("%.2f Go read"%(i/1e9))
			app.processEvents()

		try:
			datakept=data[-sizetokeep:]
			data = datakept+os.read(fd, inc)
			lendataloaded = len(data)-len(datakept)   #should be inc
			for text in patternlist:
				if text in data:
					BlocksToInspect[text].append([i-len(datakept), data, len(datakept)])
					pass
			sizetokeep=20   # 20 because all the patterns have a len<20. Could be higher.
			i += lendataloaded
		except Exception as exc:
			if lendataloaded%512>0:
				raise Exception("SPOD error 1: %d, %d"%(lendataloaded, i-len(datakept)))
			os.lseek(fd, lendataloaded, os.SEEK_CUR)
			displayWrite(str(exc))
			i += lendataloaded
			continue
	os.close(fd)

	AllOffsets=dict(map(lambda x:[x,[]], patternlist))
	for text,blocks in BlocksToInspect.items():
		for offset,data,ldk in blocks:  #ldk = len(datakept)
			offsetslist=[offset+m.start() for m in re.finditer(text, data)]
			AllOffsets[text].extend(offsetslist)

	AllOffsets['PRFdevice']=device
	AllOffsets['PRFdt']=time.time()-tzero
	AllOffsets['PRFsize']=i
	return AllOffsets

def multiextract(s, ll):
	r=[]
	cursor=0
	for length in ll:
		r.append(s[cursor:cursor+length])
		cursor+=length
	if s[cursor:]!='':
		r.append(s[cursor:])
	return r

class RecovCkey(object):
	def __init__(self, epk, pk):
		self.encrypted_pk=epk
		self.public_key=pk
		self.mkey=None
		self.privkey=None


class RecovMkey(object):
	def __init__(self, ekey, salt, nditer, ndmethod, nid):
		self.encrypted_key=ekey
		self.salt=salt
		self.iterations=nditer
		self.method=ndmethod
		self.id=nid

def readpartfile(fd, offset, length):   #make everything 512*n because of windows...
	rest=offset%512
	new_offset=offset-rest
	big_length=512*(int((length+rest-1)/512)+1)
	os.lseek(fd, new_offset, os.SEEK_SET)
	d=os.read(fd, big_length)
	return d[rest:rest+length]

def recov_ckey(fd, offset):
	d=readpartfile(fd, offset-49, 122)
	me=multiextract(d, [1,48,4,4,1])

	checks=[]
	checks.append([0, '30'])
	checks.append([3, '636b6579'])
	if sum(map(lambda x:int(me[x[0]]!=x[1].decode('hex')), checks)):  #number of false statements
		return None

	return me

def recov_mkey(fd, offset):
	d=readpartfile(fd, offset-72, 84)
	me=multiextract(d, [4,48,1,8,4,4,1,2,8,4])

	checks=[]
	checks.append([0, '43000130'])
	checks.append([2, '08'])
	checks.append([6, '00'])
	checks.append([8, '090001046d6b6579'])
	if sum(map(lambda x:int(me[x[0]]!=x[1].decode('hex')), checks)):  #number of false statements
		return None

	return me

def recov_uckey(fd, offset):
	checks=[]

	d=readpartfile(fd, offset-217, 223)
	if d[-7]=='\x26':
		me=multiextract(d, [2,1,4,1,32,141,33,2,1,6])

		checks.append([0, '3081'])
		checks.append([2, '02010104'])
	elif d[-7]=='\x46':
		d=readpartfile(fd, offset-282, 286)

		me=multiextract(d, [2,1,4,1,32,173,65,1,2,5])

		checks.append([0, '8201'])
		checks.append([2, '02010104'])
		checks.append([-1, '460001036b'])
	else:
		return None


	if sum(map(lambda x:int(me[x[0]]!=x[1].decode('hex')), checks)):  #number of false statements
		return None

	return me

def create_new_wallet(path, version):
	db_out = DB()

	try:
		r = db_out.open(path, "main", DB_BTREE, DB_CREATE)
	except DBError:
		r = True

	if r is not None:
		print "Couldn't open %s."%path
		sys.exit(1)

	db_out.put("0776657273696f6e".decode('hex'), ("%08x"%version).decode('hex')[::-1])
	db_out.close()

def npw_recoverkeys(device, passes, outputdir, name, ui, displayWrite, YesNoBox, app, size=102400, inc=10240):
	displayWrite('',empty=True)

	inc=max(512,inc>>9<<9)

	if not os.path.exists(outputdir):
		os.makedirs(outputdir)

	nameToDBName={'mkey':'\x09\x00\x01\x04mkey','ckey':'\x27\x00\x01\x04ckey','key':'\x00\x01\x03key',}


	if not device.startswith('PartialRecoveryFile:'):
		r=search_patterns_on_disk(device, size, inc, map(lambda x:nameToDBName[x], ['mkey', 'ckey', 'key']), displayWrite, app)
		f=open(outputdir+'/'+name+'_partial_recovery_%d.dat'%ts(), 'w')
		f.write(str(r))
		f.close()
		displayWrite("Read %.1f Go in %.1f minutes\n"%(r['PRFsize']/1e9, r['PRFdt']/60.0))
	else:
		prf=device[20:]
		f=open(prf, 'r')
		content=f.read()
		f.close()
		cmd=("z = "+content+"")
		exec cmd in locals()
		r=z
		device=r['PRFdevice']
		displayWrite("Loaded %.1f Go from %s\n"%(r['PRFsize']/1e9, device))


	try:
		otype=os.O_RDONLY|os.O_BINARY
	except:
		otype=os.O_RDONLY
	fd = os.open(device, otype)


	mkeys=[]
	crypters=[]
	syst=systype()
	for offset in r[nameToDBName['mkey']]:
		s=recov_mkey(fd, offset)
		if s==None:
			continue
		newmkey=RecovMkey(s[1],s[3],int(s[5][::-1].encode('hex'), 16),int(s[4][::-1].encode('hex'), 16),int(s[-1][::-1].encode('hex'), 16))
		mkeys.append([offset,newmkey])

	displayWrite('Found '+str(len(mkeys))+' possible wallets\n')

	ckeys=[]
	for offset in r[nameToDBName['ckey']]:
		s=recov_ckey(fd, offset)
		if s==None:
			continue
		newckey=RecovCkey(s[1], s[5][:int(s[4].encode('hex'),16)])
		ckeys.append([offset,newckey])
	displayWrite('Found '+str(len(ckeys))+' possible encrypted keys\n')


	uckeys=[]
	for offset in r[nameToDBName['key']]:
		s=recov_uckey(fd, offset)
		if s==None:
			continue
		uckeys.append(s[4])
	displayWrite('Found '+str(len(uckeys))+' possible unencrypted keys\n')

	os.close(fd)

	list_of_possible_keys_per_master_key=dict(map(lambda x:[x[1],[]], mkeys))
	for cko,ck in ckeys:
		tl=map(lambda x:[abs(x[0]-cko)]+x, mkeys)
		tl=sorted(tl, key=lambda x:x[0])
		list_of_possible_keys_per_master_key[tl[0][2]].append(ck)

	cpt=0
	mki=1
	tzero=time.time()
	if len(passes)==0:
		if len(ckeys)>0:
			displayWrite("Can't decrypt them as you didn't provide any passphrase.\n")
	else:
		for mko,mk in mkeys:
			list_of_possible_keys=list_of_possible_keys_per_master_key[mk]
			displayWrite( "\nPossible wallet #"+str(mki))
			for ppi,pp in enumerate(passes):
				displayWrite( "\n    with passphrase #"+str(ppi+1)+"  ")
				failures_in_a_row=0
				res = crypter.SetKeyFromPassphrase(pp, mk.salt, mk.iterations, mk.method)
				if res == 0:
					displayWrite("\nUnsupported derivation method\n")
					sys.exit(1)
				masterkey = crypter.Decrypt(mk.encrypted_key)
				crypter.SetKey(masterkey)
				for ck in list_of_possible_keys:
					if cpt%10==9 and failures_in_a_row==0:
						displayWrite('.')
					if failures_in_a_row>5:
						break
					crypter.SetIV(Hash(ck.public_key))
					secret = crypter.Decrypt(ck.encrypted_pk)
					compressed = ck.public_key[0] != '\04'


					pkey = EC_KEY(int('0x' + secret.encode('hex'), 16))
					if ck.public_key != GetPubKey(pkey, compressed):
						failures_in_a_row+=1
					else:
						failures_in_a_row=0
						ck.mkey=mk
						ck.privkey=secret
					cpt+=1
			mki+=1
		displayWrite("\n\n")
		tone=time.time()
		try:
			calcspeed=1.0*cpt/(tone-tzero)*60  #calc/min
		except:
			calcspeed=1.0
		if calcspeed==0:
			calcspeed=1.0

		ckeys_not_decrypted=filter(lambda x:x[1].privkey==None, ckeys)
		refused_to_test_all_pps=True
		if len(ckeys_not_decrypted)==0:
			displayWrite("All the found encrypted private keys have been decrypted.\n")
			return map(lambda x:x[1].privkey, ckeys)+uckeys
		else:
			displayWrite("Private keys not decrypted: %d\n"%len(ckeys_not_decrypted))
			displayWrite("Trying all the remaining possibilities (%d) might take up to %d minutes.\n"%(len(ckeys_not_decrypted)*len(passes)*len(mkeys),int(len(ckeys_not_decrypted)*len(passes)*len(mkeys)/calcspeed)))
			cont=YesNoBox("Do you want to test them?")
			if cont:
				refused_to_test_all_pps=False
				cpt=0
				for dist,mko,mk in tl:
					for ppi,pp in enumerate(passes):
						res = crypter.SetKeyFromPassphrase(pp, mk.salt, mk.iterations, mk.method)
						if res == 0:
							print "Unsupported derivation method"
							sys.exit(1)
						masterkey = crypter.Decrypt(mk.encrypted_key)
						crypter.SetKey(masterkey)
						for cko,ck in ckeys_not_decrypted:
							tl=map(lambda x:[abs(x[0]-cko)]+x, mkeys)
							tl=sorted(tl, key=lambda x:x[0])
							if mk==tl[0][2]:
								continue         #because already tested
							crypter.SetIV(Hash(ck.public_key))
							secret = crypter.Decrypt(ck.encrypted_pk)
							compressed = ck.public_key[0] != '\04'

							pkey = EC_KEY(int('0x' + secret.encode('hex'), 16))
							if ck.public_key == GetPubKey(pkey, compressed):
								ck.mkey=mk
								ck.privkey=secret
							cpt+=1

		displayWrite('\n')
		ckeys_not_decrypted=filter(lambda x:x[1].privkey==None, ckeys)
		if len(ckeys_not_decrypted)==0:
			displayWrite("All the found encrypted private keys have been finally decrypted.\n")
		elif not refused_to_test_all_pps:
			displayWrite("Private keys not decrypted: %d\n"%len(ckeys_not_decrypted))
			displayWrite("Try other passphrases or seek help.\n")
		else:
			displayWrite("Try other passphrases or seek help.\n")



	uncrypted_ckeys=filter(lambda x:x!=None, map(lambda x:x[1].privkey, ckeys))
	uckeys.extend(uncrypted_ckeys)

	return uckeys

def npw_recover(d, name, ui, displayWrite, YesNoBox, app, size=102400, inc=10240):
	displayWrite("Don't do anything until the recovery is complete.\n\n")
	device, passes, outputdir = d['device'],d['passphrases'],d['outputdir']
	if d['newpp']!=d['newppcheck']:
		return {'error':'different pps','data':'The passphrases are different'}
	newpp=d['newpp']
	if newpp=='':
		return {'error':'empty pps','data':'The passphrases are empty'}

	if isinstance(passes,str):
		passes=passes.split('\n')
	if len(device) in [2,3] and device[1]==':':
		device="\\\\.\\"+device

	recoveredKeys=npw_recoverkeys(device, passes, outputdir, name, ui, displayWrite, YesNoBox, app, size, inc)
	recoveredKeys=list(set(recoveredKeys))

#	db_env = create_env(outputdir)
	recov_wallet_name = "recovered_wallet_%s.dat"%ts()
	recov_wallet_path = outputdir+'/'+recov_wallet_name

	create_new_wallet(recov_wallet_path, 32500)
#	db_env.remove()

	if newpp!="I don't want to put a password on the recovered wallet and I know what can be the consequences.":
		db = npw_open_wallet(recov_wallet_path, True)

		NPP_salt=random_string(16).decode('hex')
		NPP_rounds=int(50000+random.random()*20000)
		NPP_method=0
		NPP_MK=random_string(64).decode('hex')
		crypter.SetKeyFromPassphrase(newpp, NPP_salt, NPP_rounds, NPP_method)
		NPP_EMK = crypter.Encrypt(NPP_MK)
		npw_update_wallet(db, 'mkey', {
			"encrypted_key": NPP_EMK,
			'nDerivationIterations' : NPP_rounds,
			'nDerivationMethod' : NPP_method,
			'nID' : 1,
			'otherParams' : ''.decode('hex'),
			"salt": NPP_salt
		})
		db.close()#remove()

	json_db=npw_read_wallet(outputdir+'/'+recov_wallet_name, newpp)['wallet']

	db = npw_open_wallet(recov_wallet_path, True)

	displayWrite("\n\nImporting:")
	for i,sec in enumerate(recoveredKeys):
		sec=sec.encode('hex')
		displayWrite("\nImporting key %4d/%d:"%(i+1, len(recoveredKeys)))
		npw_importprivkey(db, json_db, sec, "recovered: %s"%sec, None, True, passphrase=newpp)
		npw_importprivkey(db, json_db, sec+'01', "recovered: %s"%sec, None, True, passphrase=newpp)
	db.close()#remove()

	r="\n\nThe new wallet %s/%s contains the %d recovered key%s"%(outputdir, recov_wallet_name, len(recoveredKeys), iais(len(recoveredKeys)))
	displayWrite(r)
	return {'error':'none','data':'','noemptyqt':1}

def npw_write_jsonfile(filename, dic):
	filout = open(filename, 'w')
	filout.write(json.dumps(dic, sort_keys=True, indent=0))
	filout.close()

def npw_read_jsonfile(filename):
	filin = open(filename, 'r')
	txdump = filin.read()
	filin.close()
	return json.loads(txdump)


try:
	import json
	jsonencode = lambda x:json.dumps(x, sort_keys=True, indent=4)
except:
	try:
		import simplejson as json
		jsonencode = lambda x:json.dumps(x, sort_keys=True, indent=4)
	except:
		jsonencode = str

NAME        = 'NPW'
VERSION     = 00001
STRVERS     = '%d.%d.%d'%(VERSION/10000, VERSION%10000/100, VERSION%100)+'a5'
EOFSTRING   = '##\x23##EOF#####'

def strvers(v):
	return '%d.%d.%d'%(v/10000, v%10000/100, v%100)


INPUT_TYPE_LABEL    = 0x00
INPUT_TYPE_TEXT     = 0x01
INPUT_TYPE_BUTTON   = 0x02
INPUT_TYPE_FILE     = 0x03
INPUT_TYPE_COMBOBOX = 0x04
INPUT_TYPE_PASSWORD = 0x05
INPUT_TYPE_FOLDER   = 0x06
INPUT_TYPE_PTEXT    = 0x07
INPUT_TYPE_HIDDEN   = 0x08
UNREADABLE_INPUTS   = [INPUT_TYPE_LABEL, INPUT_TYPE_BUTTON]
PASSWORDS_INPUTS    = [INPUT_TYPE_PASSWORD, INPUT_TYPE_PTEXT]

ME_TYPE_PY     = 0x00
ME_TYPE_CXEXE  = 0x01
ME_TYPE_ISEXE  = 0x02
class myself(object):
	def __init__(self):
		try:
			self.type  = ME_TYPE_PY
			self.lfile = __file__
			self.ldir  = os.path.dirname(os.path.realpath(__file__))
			self.ufile = __file__
			self.udir  = os.path.dirname(os.path.realpath(__file__))
		except:
			if len(sys.argv)>1 and sys.argv[1].startswith('ISX:'):
				self.type  = ME_TYPE_ISEXE
				self.lfile = sys.executable
				self.ldir  = os.path.dirname(sys.executable)
				self.ufile = sys.argv[1][4:]
				self.udir  = os.path.dirname(sys.argv[1][4:])
			else:
				self.type  = ME_TYPE_CXEXE
				self.lfile = sys.executable
				self.ldir  = os.path.dirname(sys.executable)
				self.ufile = sys.executable
				self.udir  = os.path.dirname(sys.executable)

	def __str__(self):
		return str(self.__dict__)


ME    = myself()
DEPS  = {}
try:
	
	import socket
	import re
	import threading
	import time
	import ssl
	
	from sys import version as python_version
	from cgi import parse_header, parse_multipart
	from urlparse import parse_qs
	from BaseHTTPServer import BaseHTTPRequestHandler
	from StringIO import StringIO
	
	TERVER_TYPE_NODE  = 0x01
	TERVER_TYPE_HTTP  = 0x02
	
	class HTTPRequest(BaseHTTPRequestHandler):
		def __init__(self, request_text):
			self.vars={'GET':{},'POST':{}}
			self.rfile = StringIO(request_text)
			self.raw_requestline = self.rfile.readline()
			self.error_code = self.error_message = None
			self.parse_request()
			self.parse_vars(request_text)
	
		def send_error(self, code, message):
			self.error_code = code
			self.error_message = message
	
		def parse_vars(self,r):
			try:
				ctype, pdict = parse_header(self.headers['content-type'])
				if ctype == 'multipart/form-data':
					postvars = parse_multipart(self.rfile, pdict)
				elif ctype == 'application/x-www-form-urlencoded':
					length = int(self.headers['content-length'])
					postvars = parse_qs(self.rfile.read(length),keep_blank_values=1)
				else:
					postvars = {}
				self.vars['POST']=postvars
			except:
				pass
	
			q=r.split('\n')[0]
			if '?' in q:
				qmi=q.index('?')
				s=' '.join(q[qmi+1:].split(' ')[:-1])
				self.vars['GET']=parse_qs(s)
	
	
	def htmlpage_error404():
			return 'Erreur 404'
	
	def htmlpage_makepage(body, title='Default title'):
			return "<html>\n<head>\n<title>"+title+"</title>\n</head>\n<body>\n"+body+"\n</body>\n</html>"
	
	def parse_path(path):
			if path=='/':
				return ['', [''], '']
			if path[0]=='/':
				path=path[1:]
			if path[-1]=='/':
				path=path[:-1]
			page=path.split('/')[-1]
			return [path, path.split('/'), page]
	
	
	
	def handle_incoming_connection(csock,caddr,t):
		if t.type==TERVER_TYPE_NODE:
			return handle_incoming_connection_NODE(csock,caddr,t)
		if t.type==TERVER_TYPE_HTML:
			return handle_incoming_connection_HTML(csock,caddr,t)
	
	def handle_incoming_connection_NODE(csock,caddr,t):
		csock.shutdown(socket.SHUT_RDWR)
		csock.close()
	
	def handle_incoming_connection_HTTP(csock,caddr,t):
		cpt=1
		req = csock.recv(1024)
		while len(req)<3:
			cpt+=1
			req += csock.recv(1024)
	
		request = HTTPRequest(req)
	
		try:
			path, expath, page=parse_path(request.path)
		except:
			path, expath, page='',[''],''
		if page=='stop':
			t.stop=True
			csock.send("HTTP/1.1 200 OK\n\nStopping server on port %d."%t.port)
		elif True:
			csock.send("HTTP/1.1 200 OK\n\n"+htmlpage_makepage("Path: "+path))
		else:
			csock.send("HTTP/1.1 404 Not Found\n\n"+htmlpage_error404())
		csock.shutdown(socket.SHUT_RDWR)
		csock.close()
	
	def listen_to_connections(t):
		if t.listening:
			print '(%s)Terver already listening on port %d'%(t.name, t.port)
			return
		host = ''
		if t.port>0:
			port = t.port
		else:
			port = 8080
		sock = socket.socket(t.protocol, socket.SOCK_STREAM)
		t.socket=sock
	
		ok=False
		while not ok:
			try:
				sock.bind((host, port))
				ok=True
				t.listening=True
			except:
				port+=1
		t.port=port
	
		sock.listen(5)
		t.running=True
		p=0
		while not t.stop:
			csock, caddr = sock.accept()
			if t.ssl==True:
				try:
					csock = ssl.wrap_socket(csock, server_side=True, certfile=t.certpath, keyfile=t.certpath, ssl_version=ssl.PROTOCOL_TLSv1)
				except ssl.SSLError as e:
					if e.args[0]==1 and 'wrong version number' in  e.args[1]:
						csock.send("HTTP/1.1 426 Upgrade Required\n\nPlease use https on this port.")
						csock.shutdown(socket.SHUT_RDWR)
						csock.close()
						continue
			threading.Thread(None, t.handle, None, (csock, caddr, t)).start()
			p+=1
		t.running=False
	
	class terver(object):
		def __init__(self, port, ttype, ssl=False, handle=None, name=''):
			self.listening=False
			self.port=port
			self.socket=None
			self.protocol=socket.AF_INET
			self.stop=False
			self.type=ttype
			self.certpath='cert.pem'
			self.ssl=ssl
			self.running=False
			self.name=name
			if handle!=None:
				self.handle=handle
			else:
				if self.type==TERVER_TYPE_NODE:
					self.handle=handle_incoming_connection_NODE
				if self.type==TERVER_TYPE_HTTP:
					self.handle=handle_incoming_connection_HTTP
	
		def changeHandle(self, h):
			self.handle=h
			return self
	
	
	
	DEPS['web']=True
except:
	DEPS['web']=False

try:
	from PyQt4 import QtCore, QtGui
	QtGui.QComboBox.text=lambda self: self.currentText()
	QtGui.QPlainTextEdit.text=lambda self: self.toPlainText()
	def addtext(self,t):
		self.setPlainText(self.toPlainText()+t)
		self.repaint()
	QtGui.QPlainTextEdit.addText=addtext
	class Ui_MainWindow(object):
	    def setupUi(self, MainWindow):
	        MainWindow.setObjectName(_tr("MainWindow"))
	        MainWindow.resize(800, 600)
	        self.centralwidget = QtGui.QWidget(MainWindow)
	        self.centralwidget.setObjectName(_tr("centralwidget"))
	        self.horizontalLayout = QtGui.QHBoxLayout(self.centralwidget)
	        self.horizontalLayout.setObjectName(_tr("horizontalLayout"))
	        self.splitter = QtGui.QSplitter(self.centralwidget)
	        self.splitter.setSizeIncrement(QtCore.QSize(0, 0))
	        self.splitter.setBaseSize(QtCore.QSize(0, 0))
	        self.splitter.setOrientation(QtCore.Qt.Horizontal)
	        self.splitter.setOpaqueResize(True)
	        self.splitter.setHandleWidth(5)
	        self.splitter.setChildrenCollapsible(False)
	        self.splitter.setObjectName(_tr("splitter"))
	        self.tabWidget = QtGui.QTabWidget(self.splitter)
	        self.tabWidget.setMinimumSize(QtCore.QSize(410, 0))
	        self.tabWidget.setObjectName(_tr("tabWidget"))
	        self.tabWallet = QtGui.QWidget()
	        self.tabWallet.setObjectName(_tr("tabWallet"))
	        self.verticalLayout_7 = QtGui.QVBoxLayout(self.tabWallet)
	        self.verticalLayout_7.setObjectName(_tr("verticalLayout_7"))
	        self.tabWidget_2 = QtGui.QTabWidget(self.tabWallet)
	        self.tabWidget_2.setTabShape(QtGui.QTabWidget.Rounded)
	        self.tabWidget_2.setObjectName(_tr("tabWidget_2"))
	        self.tab_2 = QtGui.QWidget()
	        self.tab_2.setObjectName(_tr("tab_2"))
	        self.verticalLayout_8 = QtGui.QVBoxLayout(self.tab_2)
	        self.verticalLayout_8.setObjectName(_tr("verticalLayout_8"))
	        self.scrollArea = QtGui.QScrollArea(self.tab_2)
	        self.scrollArea.setWidgetResizable(True)
	        self.scrollArea.setObjectName(_tr("scrollArea"))
	        self.sAWC_Dump = QtGui.QWidget()
	        self.sAWC_Dump.setGeometry(QtCore.QRect(0, 0, 360, 451))
	        self.sAWC_Dump.setObjectName(_tr("sAWC_Dump"))
	        self.vLayoutDump = QtGui.QVBoxLayout(self.sAWC_Dump)
	        self.vLayoutDump.setObjectName(_tr("vLayoutDump"))
	        spacerItem = QtGui.QSpacerItem(20, 430, QtGui.QSizePolicy.Minimum, QtGui.QSizePolicy.Expanding)
	        self.vLayoutDump.addItem(spacerItem)
	        self.scrollArea.setWidget(self.sAWC_Dump)
	        self.verticalLayout_8.addWidget(self.scrollArea)
	        self.tabWidget_2.addTab(self.tab_2, _tr(""))
	        self.tab_3 = QtGui.QWidget()
	        self.tab_3.setObjectName(_tr("tab_3"))
	        self.verticalLayout_10 = QtGui.QVBoxLayout(self.tab_3)
	        self.verticalLayout_10.setObjectName(_tr("verticalLayout_10"))
	        self.scrollArea_8 = QtGui.QScrollArea(self.tab_3)
	        self.scrollArea_8.setWidgetResizable(True)
	        self.scrollArea_8.setObjectName(_tr("scrollArea_8"))
	        self.sAWC_Info = QtGui.QWidget()
	        self.sAWC_Info.setGeometry(QtCore.QRect(0, 0, 360, 451))
	        self.sAWC_Info.setObjectName(_tr("sAWC_Info"))
	        self.vLayoutInfo = QtGui.QVBoxLayout(self.sAWC_Info)
	        self.vLayoutInfo.setObjectName(_tr("vLayoutInfo"))
	        spacerItem1 = QtGui.QSpacerItem(20, 430, QtGui.QSizePolicy.Minimum, QtGui.QSizePolicy.Expanding)
	        self.vLayoutInfo.addItem(spacerItem1)
	        self.scrollArea_8.setWidget(self.sAWC_Info)
	        self.verticalLayout_10.addWidget(self.scrollArea_8)
	        self.tabWidget_2.addTab(self.tab_3, _tr(""))
	        self.tab = QtGui.QWidget()
	        self.tab.setObjectName(_tr("tab"))
	        self.verticalLayout_9 = QtGui.QVBoxLayout(self.tab)
	        self.verticalLayout_9.setObjectName(_tr("verticalLayout_9"))
	        self.scrollArea_7 = QtGui.QScrollArea(self.tab)
	        self.scrollArea_7.setWidgetResizable(True)
	        self.scrollArea_7.setObjectName(_tr("scrollArea_7"))
	        self.sAWC_Import = QtGui.QWidget()
	        self.sAWC_Import.setGeometry(QtCore.QRect(0, 0, 360, 451))
	        self.sAWC_Import.setObjectName(_tr("sAWC_Import"))
	        self.vLayoutImport = QtGui.QVBoxLayout(self.sAWC_Import)
	        self.vLayoutImport.setObjectName(_tr("vLayoutImport"))
	        spacerItem2 = QtGui.QSpacerItem(20, 430, QtGui.QSizePolicy.Minimum, QtGui.QSizePolicy.Expanding)
	        self.vLayoutImport.addItem(spacerItem2)
	        self.scrollArea_7.setWidget(self.sAWC_Import)
	        self.verticalLayout_9.addWidget(self.scrollArea_7)
	        self.tabWidget_2.addTab(self.tab, _tr(""))
	        self.tab_4 = QtGui.QWidget()
	        self.tab_4.setObjectName(_tr("tab_4"))
	        self.verticalLayout = QtGui.QVBoxLayout(self.tab_4)
	        self.verticalLayout.setObjectName(_tr("verticalLayout"))
	        self.scrollArea_2 = QtGui.QScrollArea(self.tab_4)
	        self.scrollArea_2.setWidgetResizable(True)
	        self.scrollArea_2.setObjectName(_tr("scrollArea_2"))
	        self.sAWC_Delete = QtGui.QWidget()
	        self.sAWC_Delete.setGeometry(QtCore.QRect(0, 0, 360, 451))
	        self.sAWC_Delete.setObjectName(_tr("sAWC_Delete"))
	        self.vLayoutDelete = QtGui.QVBoxLayout(self.sAWC_Delete)
	        self.vLayoutDelete.setObjectName(_tr("vLayoutDelete"))
	        spacerItem3 = QtGui.QSpacerItem(20, 430, QtGui.QSizePolicy.Minimum, QtGui.QSizePolicy.Expanding)
	        self.vLayoutDelete.addItem(spacerItem3)
	        self.scrollArea_2.setWidget(self.sAWC_Delete)
	        self.verticalLayout.addWidget(self.scrollArea_2)
	        self.tabWidget_2.addTab(self.tab_4, _tr(""))
	        self.verticalLayout_7.addWidget(self.tabWidget_2)
	        self.tabWidget.addTab(self.tabWallet, _tr(""))
	        self.tabFeatureSigning = QtGui.QWidget()
	        self.tabFeatureSigning.setObjectName(_tr("tabFeatureSigning"))
	        self.verticalLayout_3 = QtGui.QVBoxLayout(self.tabFeatureSigning)
	        self.verticalLayout_3.setObjectName(_tr("verticalLayout_3"))
	        self.scrollArea_4 = QtGui.QScrollArea(self.tabFeatureSigning)
	        self.scrollArea_4.setWidgetResizable(True)
	        self.scrollArea_4.setObjectName(_tr("scrollArea_4"))
	        self.sAWC_Signing = QtGui.QWidget()
	        self.sAWC_Signing.setGeometry(QtCore.QRect(0, 0, 384, 495))
	        self.sAWC_Signing.setObjectName(_tr("sAWC_Signing"))
	        self.vLayoutSigning = QtGui.QVBoxLayout(self.sAWC_Signing)
	        self.vLayoutSigning.setObjectName(_tr("vLayoutSigning"))
	        spacerItem4 = QtGui.QSpacerItem(20, 474, QtGui.QSizePolicy.Minimum, QtGui.QSizePolicy.Expanding)
	        self.vLayoutSigning.addItem(spacerItem4)
	        self.scrollArea_4.setWidget(self.sAWC_Signing)
	        self.verticalLayout_3.addWidget(self.scrollArea_4)
	        self.tabWidget.addTab(self.tabFeatureSigning, _tr(""))
	        self.tabFeatureRecover = QtGui.QWidget()
	        self.tabFeatureRecover.setObjectName(_tr("tabFeatureRecover"))
	        self.verticalLayout_5 = QtGui.QVBoxLayout(self.tabFeatureRecover)
	        self.verticalLayout_5.setObjectName(_tr("verticalLayout_5"))
	        self.scrollArea_5 = QtGui.QScrollArea(self.tabFeatureRecover)
	        self.scrollArea_5.setWidgetResizable(True)
	        self.scrollArea_5.setObjectName(_tr("scrollArea_5"))
	        self.sAWC_Recover = QtGui.QWidget()
	        self.sAWC_Recover.setGeometry(QtCore.QRect(0, 0, 384, 495))
	        self.sAWC_Recover.setObjectName(_tr("sAWC_Recover"))
	        self.vLayoutRecover = QtGui.QVBoxLayout(self.sAWC_Recover)
	        self.vLayoutRecover.setObjectName(_tr("vLayoutRecover"))
	        spacerItem5 = QtGui.QSpacerItem(20, 474, QtGui.QSizePolicy.Minimum, QtGui.QSizePolicy.Expanding)
	        self.vLayoutRecover.addItem(spacerItem5)
	        self.scrollArea_5.setWidget(self.sAWC_Recover)
	        self.verticalLayout_5.addWidget(self.scrollArea_5)
	        self.tabWidget.addTab(self.tabFeatureRecover, _tr(""))
	        self.tabFeatureECDSA = QtGui.QWidget()
	        self.tabFeatureECDSA.setObjectName(_tr("tabFeatureECDSA"))
	        self.verticalLayout_2 = QtGui.QVBoxLayout(self.tabFeatureECDSA)
	        self.verticalLayout_2.setObjectName(_tr("verticalLayout_2"))
	        self.scrollArea_3 = QtGui.QScrollArea(self.tabFeatureECDSA)
	        self.scrollArea_3.setWidgetResizable(True)
	        self.scrollArea_3.setObjectName(_tr("scrollArea_3"))
	        self.sAWC_ECDSA = QtGui.QWidget()
	        self.sAWC_ECDSA.setGeometry(QtCore.QRect(0, 0, 384, 495))
	        self.sAWC_ECDSA.setObjectName(_tr("sAWC_ECDSA"))
	        self.vLayoutECDSA = QtGui.QVBoxLayout(self.sAWC_ECDSA)
	        self.vLayoutECDSA.setObjectName(_tr("vLayoutECDSA"))
	        spacerItem6 = QtGui.QSpacerItem(20, 474, QtGui.QSizePolicy.Minimum, QtGui.QSizePolicy.Expanding)
	        self.vLayoutECDSA.addItem(spacerItem6)
	        self.scrollArea_3.setWidget(self.sAWC_ECDSA)
	        self.verticalLayout_2.addWidget(self.scrollArea_3)
	        self.tabWidget.addTab(self.tabFeatureECDSA, _tr(""))
	        self.tabFeatureTrezor = QtGui.QWidget()
	        self.tabFeatureTrezor.setObjectName(_tr("tabFeatureTrezor"))
	        self.verticalLayout_6 = QtGui.QVBoxLayout(self.tabFeatureTrezor)
	        self.verticalLayout_6.setObjectName(_tr("verticalLayout_6"))
	        self.scrollArea_6 = QtGui.QScrollArea(self.tabFeatureTrezor)
	        self.scrollArea_6.setWidgetResizable(True)
	        self.scrollArea_6.setObjectName(_tr("scrollArea_6"))
	        self.sAWC_Trezor = QtGui.QWidget()
	        self.sAWC_Trezor.setGeometry(QtCore.QRect(0, 0, 384, 495))
	        self.sAWC_Trezor.setObjectName(_tr("sAWC_Trezor"))
	        self.vLayoutTrezor = QtGui.QVBoxLayout(self.sAWC_Trezor)
	        self.vLayoutTrezor.setObjectName(_tr("vLayoutTrezor"))
	        spacerItem7 = QtGui.QSpacerItem(20, 474, QtGui.QSizePolicy.Minimum, QtGui.QSizePolicy.Expanding)
	        self.vLayoutTrezor.addItem(spacerItem7)
	        self.scrollArea_6.setWidget(self.sAWC_Trezor)
	        self.verticalLayout_6.addWidget(self.scrollArea_6)
	        self.tabWidget.addTab(self.tabFeatureTrezor, _tr(""))
	        self.tabFeatureElectrum = QtGui.QWidget()
	        self.tabFeatureElectrum.setObjectName(_tr("tabFeatureElectrum"))
	        self.verticalLayout_11 = QtGui.QVBoxLayout(self.tabFeatureElectrum)
	        self.verticalLayout_11.setObjectName(_tr("verticalLayout_11"))
	        self.scrollArea_10 = QtGui.QScrollArea(self.tabFeatureElectrum)
	        self.scrollArea_10.setWidgetResizable(True)
	        self.scrollArea_10.setObjectName(_tr("scrollArea_10"))
	        self.sAWC_Electrum = QtGui.QWidget()
	        self.sAWC_Electrum.setGeometry(QtCore.QRect(0, 0, 384, 495))
	        self.sAWC_Electrum.setObjectName(_tr("sAWC_Electrum"))
	        self.vLayoutElectrum = QtGui.QVBoxLayout(self.sAWC_Electrum)
	        self.vLayoutElectrum.setObjectName(_tr("vLayoutElectrum"))
	        spacerItem8 = QtGui.QSpacerItem(20, 40, QtGui.QSizePolicy.Minimum, QtGui.QSizePolicy.Expanding)
	        self.vLayoutElectrum.addItem(spacerItem8)
	        self.scrollArea_10.setWidget(self.sAWC_Electrum)
	        self.verticalLayout_11.addWidget(self.scrollArea_10)
	        self.tabWidget.addTab(self.tabFeatureElectrum, _tr(""))
	        self.tabFeatureTransactions = QtGui.QWidget()
	        self.tabFeatureTransactions.setObjectName(_tr("tabFeatureTransactions"))
	        self.tabWidget.addTab(self.tabFeatureTransactions, _tr(""))
	        self.tabFeatureContent = QtGui.QWidget()
	        self.tabFeatureContent.setObjectName(_tr("tabFeatureContent"))
	        self.tabWidget.addTab(self.tabFeatureContent, _tr(""))
	        self.tabFeatureMisc = QtGui.QWidget()
	        self.tabFeatureMisc.setObjectName(_tr("tabFeatureMisc"))
	        self.verticalLayout_4 = QtGui.QVBoxLayout(self.tabFeatureMisc)
	        self.verticalLayout_4.setObjectName(_tr("verticalLayout_4"))
	        self.scrollArea_9 = QtGui.QScrollArea(self.tabFeatureMisc)
	        self.scrollArea_9.setWidgetResizable(True)
	        self.scrollArea_9.setObjectName(_tr("scrollArea_9"))
	        self.sAWC_Misc = QtGui.QWidget()
	        self.sAWC_Misc.setGeometry(QtCore.QRect(0, 0, 384, 495))
	        self.sAWC_Misc.setObjectName(_tr("sAWC_Misc"))
	        self.vLayoutMisc = QtGui.QVBoxLayout(self.sAWC_Misc)
	        self.vLayoutMisc.setObjectName(_tr("vLayoutMisc"))
	        spacerItem9 = QtGui.QSpacerItem(20, 474, QtGui.QSizePolicy.Minimum, QtGui.QSizePolicy.Expanding)
	        self.vLayoutMisc.addItem(spacerItem9)
	        self.scrollArea_9.setWidget(self.sAWC_Misc)
	        self.verticalLayout_4.addWidget(self.scrollArea_9)
	        self.tabWidget.addTab(self.tabFeatureMisc, _tr(""))
	        self.plainTextEdit = QtGui.QPlainTextEdit(self.splitter)
	        self.plainTextEdit.setSizeIncrement(QtCore.QSize(0, 0))
	        self.plainTextEdit.setReadOnly(True)
	        self.plainTextEdit.setPlainText(_tr(""))
	        self.plainTextEdit.setObjectName(_tr("plainTextEdit"))
	        self.horizontalLayout.addWidget(self.splitter)
	        MainWindow.setCentralWidget(self.centralwidget)
	        self.menubar = QtGui.QMenuBar(MainWindow)
	        self.menubar.setGeometry(QtCore.QRect(0, 0, 800, 21))
	        self.menubar.setObjectName(_tr("menubar"))
	        self.menuFile = QtGui.QMenu(self.menubar)
	        self.menuFile.setObjectName(_tr("menuFile"))
	        self.menuEdit = QtGui.QMenu(self.menubar)
	        self.menuEdit.setObjectName(_tr("menuEdit"))
	        self.menu = QtGui.QMenu(self.menubar)
	        self.menu.setObjectName(_tr("menu"))
	        MainWindow.setMenuBar(self.menubar)
	        self.statusbar = QtGui.QStatusBar(MainWindow)
	        self.statusbar.setObjectName(_tr("statusbar"))
	        MainWindow.setStatusBar(self.statusbar)
	        self.actionAbout_NPW = QtGui.QAction(MainWindow)
	        self.actionAbout_NPW.setObjectName(_tr("actionAbout_NPW"))
	        self.actionSettings = QtGui.QAction(MainWindow)
	        self.actionSettings.setObjectName(_tr("actionSettings"))
	        self.actionUpdate = QtGui.QAction(MainWindow)
	        self.actionUpdate.setObjectName(_tr("actionUpdate"))
	        self.menuFile.addAction(self.actionUpdate)
	        self.menu.addAction(self.actionAbout_NPW)
	        self.menubar.addAction(self.menuFile.menuAction())
	        self.menubar.addAction(self.menuEdit.menuAction())
	        self.menubar.addAction(self.menu.menuAction())
	
	        self.retranslateUi(MainWindow)
	        self.tabWidget.setCurrentIndex(0)
	        self.tabWidget_2.setCurrentIndex(0)
	        QtCore.QObject.connect(self.actionUpdate, QtCore.SIGNAL(_tr("triggered()")), self.actionSettings.hover)
	        QtCore.QMetaObject.connectSlotsByName(MainWindow)
	
	    def retranslateUi(self, MainWindow):
	        MainWindow.setWindowTitle(_translate("MainWindow", NAME+" v"+STRVERS, None))
	        self.tabWidget_2.setTabText(self.tabWidget_2.indexOf(self.tab_2), _translate("MainWindow", "Dump", None))
	        self.tabWidget_2.setTabText(self.tabWidget_2.indexOf(self.tab_3), _translate("MainWindow", "Info", None))
	        self.tabWidget_2.setTabText(self.tabWidget_2.indexOf(self.tab), _translate("MainWindow", "Import", None))
	        self.tabWidget_2.setTabText(self.tabWidget_2.indexOf(self.tab_4), _translate("MainWindow", "Delete", None))
	        self.tabWidget.setTabText(self.tabWidget.indexOf(self.tabWallet), _translate("MainWindow", "Wallet", None))
	        self.tabWidget.setTabText(self.tabWidget.indexOf(self.tabFeatureSigning), _translate("MainWindow", "Messages", None))
	        self.tabWidget.setTabText(self.tabWidget.indexOf(self.tabFeatureRecover), _translate("MainWindow", "Recover", None))
	        self.tabWidget.setTabText(self.tabWidget.indexOf(self.tabFeatureECDSA), _translate("MainWindow", "ECDSA", None))
	        self.tabWidget.setTabText(self.tabWidget.indexOf(self.tabFeatureTrezor), _translate("MainWindow", "Trezor", None))
	        self.tabWidget.setTabText(self.tabWidget.indexOf(self.tabFeatureElectrum), _translate("MainWindow", "Electrum", None))
	        self.tabWidget.setTabText(self.tabWidget.indexOf(self.tabFeatureTransactions), _translate("MainWindow", "Transactions", None))
	        self.tabWidget.setTabText(self.tabWidget.indexOf(self.tabFeatureContent), _translate("MainWindow", "Content", None))
	        self.tabWidget.setTabText(self.tabWidget.indexOf(self.tabFeatureMisc), _translate("MainWindow", "Misc", None))
	        self.menuFile.setTitle(_translate("MainWindow", "File", None))
	        self.menuEdit.setTitle(_translate("MainWindow", "Edit", None))
	        self.menu.setTitle(_translate("MainWindow", "?", None))
	        self.actionAbout_NPW.setText(_translate("MainWindow", "About NPW", None))
	        self.actionSettings.setText(_translate("MainWindow", "Settings", None))
	        self.actionUpdate.setText(_translate("MainWindow", "Update", None))
	
	
	

	class Ui_Dialog(object):
	    def setupUi(self, Dialog):
	        Dialog.setObjectName(_tr("Dialog"))
	        Dialog.resize(564, 238)
	        self.verticalLayout_2 = QtGui.QVBoxLayout(Dialog)
	        self.verticalLayout_2.setObjectName(_tr("verticalLayout_2"))
	        spacerItem = QtGui.QSpacerItem(20, 40, QtGui.QSizePolicy.Minimum, QtGui.QSizePolicy.Expanding)
	        self.verticalLayout_2.addItem(spacerItem)
	        self.verticalLayout = QtGui.QVBoxLayout()
	        self.verticalLayout.setContentsMargins(-1, 5, 0, 5)
	        self.verticalLayout.setObjectName(_tr("verticalLayout"))
	        self.horizontalLayout_3 = QtGui.QHBoxLayout()
	        self.horizontalLayout_3.setContentsMargins(-1, 0, -1, -1)
	        self.horizontalLayout_3.setObjectName(_tr("horizontalLayout_3"))
	        self.label = QtGui.QLabel(Dialog)
	        self.label.setObjectName(_tr("label"))
	        self.horizontalLayout_3.addWidget(self.label)
	        self.label_2 = QtGui.QLabel(Dialog)
	        self.label_2.setObjectName(_tr("label_2"))
	        self.horizontalLayout_3.addWidget(self.label_2)
	        self.verticalLayout.addLayout(self.horizontalLayout_3)
	        self.label_3 = QtGui.QLabel(Dialog)
	        self.label_3.setTextInteractionFlags(QtCore.Qt.LinksAccessibleByMouse|QtCore.Qt.TextSelectableByMouse)
	        self.label_3.setObjectName(_tr("label_3"))
	        self.verticalLayout.addWidget(self.label_3)
	        self.verticalLayout_2.addLayout(self.verticalLayout)
	        spacerItem1 = QtGui.QSpacerItem(20, 40, QtGui.QSizePolicy.Minimum, QtGui.QSizePolicy.Expanding)
	        self.verticalLayout_2.addItem(spacerItem1)
	        self.horizontalLayout_2 = QtGui.QHBoxLayout()
	        self.horizontalLayout_2.setSizeConstraint(QtGui.QLayout.SetMinAndMaxSize)
	        self.horizontalLayout_2.setObjectName(_tr("horizontalLayout_2"))
	        spacerItem2 = QtGui.QSpacerItem(40, 20, QtGui.QSizePolicy.Expanding, QtGui.QSizePolicy.Minimum)
	        self.horizontalLayout_2.addItem(spacerItem2)
	        self.horizontalLayout = QtGui.QHBoxLayout()
	        self.horizontalLayout.setObjectName(_tr("horizontalLayout"))
	        self.pushButton = QtGui.QPushButton(Dialog)
	        self.pushButton.setObjectName(_tr("pushButton"))
	        self.horizontalLayout.addWidget(self.pushButton)
	        self.horizontalLayout_2.addLayout(self.horizontalLayout)
	        self.verticalLayout_2.addLayout(self.horizontalLayout_2)
	
	        self.retranslateUi(Dialog)
	        QtCore.QObject.connect(self.pushButton, QtCore.SIGNAL(_tr("clicked()")), Dialog.close)
	        QtCore.QMetaObject.connectSlotsByName(Dialog)
	
	    def retranslateUi(self, Dialog):
	        Dialog.setWindowTitle(_translate("Dialog", "About", None))
	        self.label.setText(_translate("Dialog", "<html><head/><body><p align=\"right\">NPW</p></body></html>", None))
	        self.label_2.setText(_translate("Dialog", "0.0.0", None))
	        self.label_3.setText(_translate("Dialog", "<html><head/><body><p align=\"center\">NPW is a Bitcoin tool with many features.<br/><br/><br/>It is developped by jackjack (<a href=\"https://bitcointalk.org/index.php?action=profile;u=21053\"><span style=\" text-decoration: underline; color:#0000ff;\">bitcointalk</span></a>, <a href=\"https://github.com/jackjack-jj\"><span style=\" text-decoration: underline; color:#0000ff;\">github</span></a>)<br/><br/><span style=\" font-weight:600;\">Donation addresses</span><br/>jackjack: 19QkqAza7BHFTuoz9N8UQkryP4E9jHo4N3<br/>NPW development: 19QkqAza7BHFTuoz9N8UQkryP4E9jHo4N3</p></body></html>", None))
	        self.pushButton.setText(_translate("Dialog", "OK", None))
	
	
	
	def displayAboutWindow(u):
		u.AboutWindow = QtGui.QWidget()
		ui2 = Ui_Dialog()
		ui2.setupUi(u.AboutWindow)
		ui2.label.setText('<html><head/><body><p align="right">'+NAME+'</p></body></html>')
		ui2.label_2.setText(STRVERS)
		u.AboutWindow.show()

 	DEPS['Qt']=True
except:
    DEPS['Qt']=False

try:
	from translation import _tr, _translate
except:
	def _tr(txt,lg=''):
		return txt
	def _translate(m,t,b):
		return t

CSS='''<style type="text/css">
  a {
    color: blue;
	text-decoration:none;
  }
  </style>'''

try:
	_p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2FL
except:
	print "Python 3 is not supported yet, you need Python 2.7.x"
	exit(1)
_r = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141L
_b = 0x0000000000000000000000000000000000000000000000000000000000000007L
_a = 0x0000000000000000000000000000000000000000000000000000000000000000L
_Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798L
_Gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8L

##            NEVER CHANGE THE FOLLOWING VARIABLES!!           ##
OTHERLVURL     = 'https://raw.github.com/jackjack-jj/npwtest/master/bin'
LASTVERSURL    = 'https://raw.github.com/jackjack-jj/npwtest/master/npw.py'
SIGNINGADDRESS = '1Azzay7wH1FnDE5yZMPU57y75SuT4DbGc7'
SIGNATURE      = ''

ko = 1e3
kio = 1024
Mo = 1e6
Mio = 1024 ** 2
Go = 1e9
Gio = 1024 ** 3
To = 1e12
Tio = 1024 ** 4

############################################
############################################
def systype():
	if platform.system() == "Darwin":
		return 'Mac'
	elif platform.system() == "Windows":
		return 'Win'
	return 'Linux'

def ts():
	return int(time.mktime(datetime.now().timetuple()))

class DataInput(object):
	def __init__(self, type='', name='', text='', fct=None, texts=[], desc='', pw=False):
		self.type=type
		self.name=name
		self.text=text
		self.fct=fct
		self.texts=texts
		self.desc=desc
		self.password=pw

def GetArg(a, d=''):
	for i in range(1,len(sys.argv)):
		if sys.argv[i-1]==a:
			return sys.argv[i]
	return d

def GetArgs(a, d=[]):
	r={}
	while len(d)<len(a):
		d.append('')
	for i,arg in enumerate(a):
		r[arg]=GetArg(arg,d[i])
	return r

def GetFlag(a, d=''):
	for i in range(1,len(sys.argv)):
		if sys.argv[i]==a:
			return True
	return False

class CurveFp( object ):
	def __init__( self, p, a, b ):
		self.__p = p
		self.__a = a
		self.__b = b

	def p( self ):
		return self.__p

	def a( self ):
		return self.__a

	def b( self ):
		return self.__b

	def contains_point( self, x, y ):
		return ( y * y - ( x * x * x + self.__a * x + self.__b ) ) % self.__p == 0

class Point( object ):
	def __init__( self, curve, x, y, order = None ):
		self.__curve = curve
		self.__x = x
		self.__y = y
		self.__order = order
		if self.__curve: assert self.__curve.contains_point( x, y )
		if order: assert self * order == INFINITY

	def __sub__( self, other ):
		return self + other.negative_self()

	def __add__( self, other ):
		if other == INFINITY: return self
		if self == INFINITY: return other
		assert self.__curve == other.__curve
		if self.__x == other.__x:
			if ( self.__y + other.__y ) % self.__curve.p() == 0:
				return INFINITY
			else:
				return self.double()

		p = self.__curve.p()
		l = ( ( other.__y - self.__y ) * \
					inverse_mod( other.__x - self.__x, p ) ) % p
		x3 = ( l * l - self.__x - other.__x ) % p
		y3 = ( l * ( self.__x - x3 ) - self.__y ) % p
		return Point( self.__curve, x3, y3 )

	def __mul__( self, other ):
		def leftmost_bit( x ):
			assert x > 0
			result = 1L
			while result <= x: result = 2 * result
			return result / 2

		e = other
		if self.__order: e = e % self.__order
		if e == 0: return INFINITY
		if self == INFINITY: return INFINITY
		assert e > 0
		e3 = 3 * e
		negative_self = Point( self.__curve, self.__x, -self.__y, self.__order )
		i = leftmost_bit( e3 ) / 2
		result = self
		while i > 1:
			result = result.double()
			if ( e3 & i ) != 0 and ( e & i ) == 0: result = result + self
			if ( e3 & i ) == 0 and ( e & i ) != 0: result = result + negative_self
			i = i / 2
		return result

	def negative_self(self):
		return Point( self.__curve, self.__x, -self.__y, self.__order )

	def __rmul__( self, other ):
		return self * other

	def __str__( self ):
		if self == INFINITY: return "infinity"
		return "(%d,%d)" % ( self.__x, self.__y )

	def double( self ):
		if self == INFINITY:
			return INFINITY

		p = self.__curve.p()
		a = self.__curve.a()
		l = ( ( 3 * self.__x * self.__x + a ) * \
					inverse_mod( 2 * self.__y, p ) ) % p
		x3 = ( l * l - 2 * self.__x ) % p
		y3 = ( l * ( self.__x - x3 ) - self.__y ) % p
		return Point( self.__curve, x3, y3 )

	def x( self ):
		return self.__x

	def y( self ):
		return self.__y

	def curve( self ):
		return self.__curve

	def order( self ):
		return self.__order

	def ser( self, comp=True ):
		if comp:
			return ( ('%02x'%(2+(self.__y&1)))+('%064x'%self.__x) ).decode('hex')
		return ( '04'+('%064x'%self.__x)+('%064x'%self.__y) ).decode('hex')

def inversetxid(txid):
	return txid.decode('hex')[::-1].encode('hex')

GetPubKey = lambda p,c: p.pubkey.ser(c)
def regenerate_key(sec):
	b = ASecretToSecret(sec)
	if not b:
		return False
	b = b[0:32]
	secret = int('0x' + b.encode('hex'), 16)
	return EC_KEY(secret)

def GetPrivKey(pkey, compressed=False):
	return i2d_ECPrivateKey(pkey, compressed)

def GetSecret(pkey):
	return ('%064x' % pkey.secret).decode('hex')

def i2d_ECPrivateKey(pkey, compressed=False):
	if compressed:
		part3='a08185308182020101302c06072a8648ce3d0101022100'
		key = '3081d30201010420' + \
			'%064x' % pkey.secret + \
			part3 + \
			'%064x' % _p + \
			'3006040100040107042102' + \
			'%064x' % _Gx + \
			'022100' + \
			'%064x' % _r + \
			'020101a124032200'
	else:
		part3='a081a53081a2020101302c06072a8648ce3d0101022100'
		key = '308201130201010420' + \
			'%064x' % pkey.secret + \
			part3 + \
			'%064x' % _p + \
			'3006040100040107044104' + \
			'%064x' % _Gx + \
			'%064x' % _Gy + \
			'022100' + \
			'%064x' % _r + \
			'020101a144034200'

	return key.decode('hex') + GetPubKey(pkey, compressed)

INFINITY = Point( None, None, None )
curveBitcoin = curve_secp256k1 = CurveFp(_p, _a, _b)
generator_secp256k1 = Point( curve_secp256k1, _Gx, _Gy, _r )

def ECC_YfromX(x,curved=curveBitcoin, odd=True):
	_p = curved.p()
	_a = curved.a()
	_b = curved.b()
	for offset in range(128):
		Mx=x+offset
		My2 = pow(Mx, 3, _p) + _a * pow(Mx, 2, _p) + _b % _p
		My = pow(My2, (_p+1)/4, _p )

		if curved.contains_point(Mx,My):
			if odd == bool(My&1):
				return [My,offset]
			return [_p-My,offset]
	raise Exception('ECC_YfromX: No Y found')

def inverse_mod( a, m ):
	if a < 0 or m <= a: a = a % m
	c, d = a, m
	uc, vc, ud, vd = 1, 0, 0, 1
	while c != 0:
		q, c, d = divmod( d, c ) + ( c, )
		uc, vc, ud, vd = ud - q*uc, vd - q*vc, uc, vc
	assert d == 1
	if ud > 0: return ud
	else: return ud + m

def str_to_long(b):
	res = 0
	pos = 1
	for a in reversed(b):
		res += ord(a) * pos
		pos *= 256
	return res

def str_to_long(b):
	res = 0
	pos = 1
	for a in reversed(b):
		res += ord(a) * pos
		pos *= 256
	return res

def PrivKeyToSecret(privkey):
	if len(privkey) == 279:
		return privkey[9:9+32]
	else:
		return privkey[8:8+32]

def SecretToASecret(secret, compressed=False, v=0):
	prefix = chr((v+128)&255)
	if v==48:  #assuming Litecoin
		prefix = chr(128)
	vchIn = prefix + secret
	if compressed: vchIn += '\01'
	return EncodeBase58Check(vchIn)

def ASecretToSecret(sec, v=0):
	vch = DecodeBase58Check(sec)
	if not vch:
		return False
	if vch[0] != chr((v+128)&255):
		print 'Warning: adress prefix seems bad (%d vs %d)'%(ord(vch[0]), (v+128)&255)
	return vch[1:]

class Public_key( object ):
	def __init__( self, generator, point, c ):
		self.curve = generator.curve()
		self.generator = generator
		self.point = point
		self.compressed = c
		n = generator.order()
		if not n:
			raise RuntimeError, "Generator point must have order."
		if not n * point == INFINITY:
			raise RuntimeError, "Generator point order is bad."
		if point.x() < 0 or n <= point.x() or point.y() < 0 or n <= point.y():
			raise RuntimeError, "Generator point has x or y out of range."

	def verify( self, hash, signature ):
		if isinstance(hash, str):
			hash=str_to_long(hash)
		G = self.generator
		n = G.order()
		r = signature.r
		s = signature.s
		if r < 1 or r > n-1: return False
		if s < 1 or s > n-1: return False
		c = inverse_mod( s, n )
		u1 = ( hash * c ) % n
		u2 = ( r * c ) % n
		xy = u1 * G + u2 * self.point
		v = xy.x() % n
		return v == r

	def ser(self,c=None):
		if c==None:
			c=self.compressed
		if c:
			pk=('%02x'%(2+(self.point.y()&1))) + '%064x' % self.point.x()
		else:
			pk='04%064x%064x' % (self.point.x(), self.point.y())

		return pk.decode('hex')

	def get_addr(self, v=0, comp=None):
		return public_key_to_bc_address(self.ser(comp), v)

class Signature( object ):
	def __init__( self, r, s ):
		self.r = r
		self.s = s

	def ser(self):
		return ("%064x%064x"%(self.r,self.s)).decode('hex')

	def der(self):
		serR='%x'%self.r
		serS='%x'%self.s
		while len(serR)%2:
			serR='0'+serR
		while len(serS)%2:
			serS='0'+serS

		if self.r>>255:
			serR='00'+serR
		if self.s>>255:
			serS='00'+serS

		return ("30%02x02%02x%s02%02x%s"%(len(serR)/2+len(serS)/2+4, len(serR)/2, serR, len(serS)/2, serS)).decode('hex')

class Private_key( object ):
	def __init__( self, public_key, secret_multiplier ):
		self.public_key = public_key
		self.secret_multiplier = secret_multiplier

	def sign( self, hash, random_k ):
		if isinstance(hash, str):
			hash=str_to_long(hash)
		G = self.public_key.generator
		n = G.order()
		k = random_k % n
		p1 = k * G
		r = p1.x()
		if r == 0: raise RuntimeError, "amazingly unlucky random number r"
		s = ( inverse_mod( k, n ) * \
					( hash + ( self.secret_multiplier * r ) % n ) ) % n
		if s == 0: raise RuntimeError, "amazingly unlucky random number s"
		return Signature( r, s )

class EC_KEY(object):
	def __init__( self, secret, c=False):
		if isinstance(secret, str):
			secret=str_to_long(secret)
		curve = CurveFp( _p, _a, _b )
		generator = Point( curve, _Gx, _Gy, _r )
		self.pubkey = Public_key( generator, generator * secret, c )
		self.privkey = Private_key( self.pubkey, secret )
		self.secret = secret

def decbin(d, l=0, rev=False):
	if l==0:
		a="%x"%d
		if len(a)%2: a='0'+a
	else:
		a=("%0"+str(2*l)+"x")%d
	a=a.decode('hex')
	if rev:
		a=a[::-1]
	return a

def decvi(d):
	if d<0xfd:
		return decbin(d)
	elif d<0xffff:
		return '\xfd'+decbin(d,2,True)
	elif d<0xffffffff:
		return '\xfe'+decbin(d,4,True)
	return '\xff'+decbin(d,8,True)

def format_msg_to_sign(msg):
    return "\x18Bitcoin Signed Message:\n"+decvi(len(msg))+msg

def hash_160(public_key):
 	md = hashlib.new('ripemd160')
	md.update(hashlib.sha256(public_key).digest())
	return md.digest()

def public_key_to_bc_address(public_key, v=0):
	h160 = hash_160(public_key)
	return hash_160_to_bc_address(h160, v)

def hash_160_to_bc_address(h160, addrtype=0):
	vh160 = chr(addrtype) + h160
	h = Hash(vh160)
	addr = vh160 + h[0:4]
	return b58encode(addr)

def bc_address_to_hash_160(addr):
	bytes = b58decode(addr, 25)
	return bytes[1:21]

def Hash(data):
	return hashlib.sha256(hashlib.sha256(data).digest()).digest()

def sha256(data):
	return hashlib.sha256(data).digest()

def sha1(data):
	return hashlib.sha1(data).digest()

__b58chars = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
__b58base = len(__b58chars)

def b58encode(v):
	long_value = 0L
	for (i, c) in enumerate(v[::-1]):
		long_value += (256**i) * ord(c)

	result = ''
	while long_value >= __b58base:
		div, mod = divmod(long_value, __b58base)
		result = __b58chars[mod] + result
		long_value = div
	result = __b58chars[long_value] + result

	nPad = 0
	for c in v:
		if c == '\0': nPad += 1
		else: break

	return (__b58chars[0]*nPad) + result

def b58decode(v, length):
	long_value = 0L
	for (i, c) in enumerate(v[::-1]):
		long_value += __b58chars.find(c) * (__b58base**i)

	result = ''
	while long_value >= 256:
		div, mod = divmod(long_value, 256)
		result = chr(mod) + result
		long_value = div
	result = chr(long_value) + result

	nPad = 0
	for c in v:
		if c == __b58chars[0]: nPad += 1
		else: break

	result = chr(0)*nPad + result
	if length is not None and len(result) != length:
		return None

	return result

def EncodeBase58Check(secret):
	hash = Hash(secret)
	return b58encode(secret + hash[0:4])

def DecodeBase58Check(sec):
	vchRet = b58decode(sec, None)
	secret = vchRet[0:-4]
	csum = vchRet[-4:]
	hash = Hash(secret)
	cs32 = hash[0:4]
	if cs32 != csum:
		return None
	else:
		return secret

class BCDataStream(object):
	def __init__(self):
		self.input = None
		self.read_cursor = 0

	def clear(self):
		self.input = None
		self.read_cursor = 0

	def write(self, bytes):	# Initialize with string of bytes
		if self.input is None:
			self.input = bytes
		else:
			self.input += bytes

	def map_file(self, file, start):	# Initialize with bytes from file
		self.input = mmap.mmap(file.fileno(), 0, access=mmap.ACCESS_READ)
		self.read_cursor = start
	def seek_file(self, position):
		self.read_cursor = position
	def close_file(self):
		self.input.close()

	def read_string(self):
		# Strings are encoded depending on length:
		# 0 to 252 :	1-byte-length followed by bytes (if any)
		# 253 to 65,535 : byte'253' 2-byte-length followed by bytes
		# 65,536 to 4,294,967,295 : byte '254' 4-byte-length followed by bytes
		# ... and the Bitcoin client is coded to understand:
		# greater than 4,294,967,295 : byte '255' 8-byte-length followed by bytes of string
		# ... but I don't think it actually handles any strings that big.
		if self.input is None:
			raise SerializationError("call write(bytes) before trying to deserialize")

		try:
			length = self.read_compact_size()
		except IndexError:
			raise SerializationError("attempt to read past end of buffer")

		return self.read_bytes(length)

	def write_string(self, string):
		# Length-encoded as with read-string
		self.write_compact_size(len(string))
		self.write(string)

	def read_bytes(self, length):
		try:
			result = self.input[self.read_cursor:self.read_cursor+length]
			self.read_cursor += length
			return result
		except IndexError:
			raise SerializationError("attempt to read past end of buffer")

		return ''

	def read_boolean(self): return self.read_bytes(1)[0] != chr(0)
	def read_int16(self): return self._read_num('<h')
	def read_uint16(self): return self._read_num('<H')
	def read_int32(self): return self._read_num('<i')
	def read_uint32(self): return self._read_num('<I')
	def read_int64(self): return self._read_num('<q')
	def read_uint64(self): return self._read_num('<Q')

	def write_boolean(self, val): return self.write(chr(bool_to_int(val)))
	def write_int16(self, val): return self._write_num('<h', val)
	def write_uint16(self, val): return self._write_num('<H', val)
	def write_int32(self, val): return self._write_num('<i', val)
	def write_uint32(self, val): return self._write_num('<I', val)
	def write_int64(self, val): return self._write_num('<q', val)
	def write_uint64(self, val): return self._write_num('<Q', val)

	def read_compact_size(self):
		size = ord(self.input[self.read_cursor])
		self.read_cursor += 1
		if size == 253:
			size = self._read_num('<H')
		elif size == 254:
			size = self._read_num('<I')
		elif size == 255:
			size = self._read_num('<Q')
		return size

	def write_compact_size(self, size):
		if size < 0:
			raise SerializationError("attempt to write size < 0")
		elif size < 253:
			 self.write(chr(size))
		elif size < 2**16:
			self.write('\xfd')
			self._write_num('<H', size)
		elif size < 2**32:
			self.write('\xfe')
			self._write_num('<I', size)
		elif size < 2**64:
			self.write('\xff')
			self._write_num('<Q', size)

	def _read_num(self, format):
		(i,) = struct.unpack_from(format, self.input, self.read_cursor)
		self.read_cursor += struct.calcsize(format)
		return i

	def _write_num(self, format, num):
		s = struct.pack(format, num)
		self.write(s)

def parse_setting(setting, vds):
	if setting[0] == "f":	# flag (boolean) settings
		return str(vds.read_boolean())
	elif setting[0:4] == "addr": # CAddress
		d = parse_CAddress(vds)
		return deserialize_CAddress(d)
	elif setting == "nTransactionFee":
		return vds.read_int64()
	elif setting == "nLimitProcessors":
		return vds.read_int32()
	return 'unknown setting'

def parse_CAddress(vds):
	d = {'ip':'0.0.0.0','port':0,'nTime': 0}
	try:
		d['nVersion'] = vds.read_int32()
		d['nTime'] = vds.read_uint32()
		d['nServices'] = vds.read_uint64()
		d['pchReserved'] = vds.read_bytes(12)
		d['ip'] = socket.inet_ntoa(vds.read_bytes(4))
		d['port'] = vds.read_uint16()
	except:
		pass
	return d

def deserialize_CAddress(d):
	return d['ip']+":"+str(d['port'])

#####################################
#####################################
#####################################
def passfct(*a):
	pass

def displayInput_Qt(i,gb,vlayout,inputlist=[]):
	if i.type==INPUT_TYPE_LABEL:
		r = QtGui.QLabel(gb)
		r.setText(i.text)
		vlayout.addWidget(r)
	elif i.type==INPUT_TYPE_TEXT:
		r = QtGui.QLineEdit(gb)
		if 'setPlaceholderText' not in dir(r):
			r.setPlaceholderText=passfct
		r.setPlaceholderText(i.text)
		vlayout.addWidget(r)
	elif i.type==INPUT_TYPE_PTEXT:
		r = QtGui.QLabel(gb)
		r.setText(i.text+': ')
		vlayout.addWidget(r)
		r = QtGui.QPlainTextEdit(gb)
		if i.password:
			r.setStyleSheet("color: white;")
		vlayout.addWidget(r)
	elif i.type==INPUT_TYPE_HIDDEN:
		r = QtGui.QLineEdit(gb)
		r.hide()
		r.setText(i.text)
	elif i.type==INPUT_TYPE_PASSWORD:
		r = QtGui.QLineEdit(gb)
		if 'setPlaceholderText' not in dir(r):
			r.setPlaceholderText=passfct
		r.setPlaceholderText(i.text)
		r.setEchoMode(QtGui.QLineEdit.Password)
		vlayout.addWidget(r)
	elif i.type==INPUT_TYPE_BUTTON:
		r = QtGui.QPushButton(gb)
		r.setText(i.text)
		vlayout.addWidget(r)
		QtCore.QObject.connect(r, QtCore.SIGNAL("clicked()"), lambda:executeResult(i.fct(dict(map(lambda x:[x,str(inputlist[x].text())], inputlist)))))
	elif i.type in [INPUT_TYPE_FILE,INPUT_TYPE_FOLDER]:
		fcts={INPUT_TYPE_FILE:QtGui.QFileDialog.getOpenFileName,INPUT_TYPE_FOLDER:QtGui.QFileDialog.getExistingDirectory}
		horizontalLayoutWidget = QtGui.QWidget(gb)
		horizontalLayout = QtGui.QHBoxLayout(horizontalLayoutWidget)
		horizontalLayout.setMargin(0)
		r = QtGui.QLineEdit(horizontalLayoutWidget)
		if 'setPlaceholderText' not in dir(r):
			r.setPlaceholderText=passfct
		r.setPlaceholderText(i.text)
		r.setReadOnly(True)
		horizontalLayout.addWidget(r)
		b = QtGui.QPushButton(horizontalLayoutWidget)
		b.setText('...')
		b.setMaximumWidth(25)
		horizontalLayout.addWidget(b)
		vlayout.addWidget(horizontalLayoutWidget)
		QtCore.QObject.connect(b, QtCore.SIGNAL("clicked()"), lambda:r.setText(fcts[i.type]()))
	elif i.type==INPUT_TYPE_COMBOBOX:
		r = QtGui.QComboBox(gb)
		map(lambda x:r.addItem(x), i.texts)
		vlayout.addWidget(r)
	else:
		return None

	return r

def addFeature_Qt(d):
	if 'noqt' in d.keys():
		return None
	ui,title,desc,inputs,page=d['ui'],d['name'],d['desc'],d['inputs'],d['page']
	pages={
		'dump':ui.vLayoutDump,
		'info':ui.vLayoutInfo,
		'import':ui.vLayoutImport,
        'ecdsa':ui.vLayoutECDSA,
        'signing':ui.vLayoutSigning,
        'recover':ui.vLayoutRecover,
        'misc':ui.vLayoutMisc,
        'electrum':ui.vLayoutElectrum,
	}
	if page not in pages.keys():
		print 'Page not found: %s (addFeature_Qt)'%page
		return None
	layout=pages[page]
	groupBox = QtGui.QGroupBox() # ui.sAWC_Dump
	vlayout = QtGui.QVBoxLayout(groupBox)
	groupBox.setTitle(title)

	inputlist={}
	for i in inputs:
		ipt=displayInput_Qt(i,groupBox,vlayout,inputlist)

		if ipt!=None and i.type not in UNREADABLE_INPUTS:
			inputlist[i.name]=ipt

	layout.insertWidget(layout.count()-1,groupBox)
	return groupBox

#####################################
#####################################
#####################################
def dic_data_error(e,d):
	return {'error':e, 'data':d}

def dic_data_noerror(d):
	return dic_data_error('none',d)

def npw_dumpwallet(d):
	data=npw_read_wallet(d['wallet'],d['passphrase'],int('0'+d['version']))
	d=jsonencode(data)
	return dic_data_noerror(d)

def npw_exec_importcsvprivkeys(d):
	filename = d['wallet']
	read_wallet = npw_read_wallet(filename, d['passphrase'])
	json_db = read_wallet['wallet']
	can_import = read_wallet['goodpp']
	if not can_import:
		return dic_data_error('bad passphrase','The given passphrase is not the good one so the private key can\'t be imported')
	db = npw_open_wallet(filename, True)
	npw_import_csv_keys_to_wallet(d['csvfile'], db, json_db, d['passphrase'])
	db.close()
	return dic_data_noerror('Done')

def npw_exec_importprivkey(d):
	filename = d['wallet']
	read_wallet = npw_read_wallet(filename, d['passphrase'])
	json_db = read_wallet['wallet']
	can_import = read_wallet['goodpp']
	if not can_import:
		return dic_data_error('bad passphrase','The given passphrase is not the good one so the private key can\'t be imported')
	db = npw_open_wallet(filename, True)
	label = d['label']
	if label == '':
		label = 'Imported with '+NAME+' '+STRVERS
	#db, json_db, sec, label, reserve, keyishex, verbose=True, addrv=0, passphrase=''
	r = npw_importprivkey(db, json_db, d['privkey'], label, 0, 'keyishex', False, 0, d['passphrase'])
	db.close()
	return dic_data_noerror('Done: '+str(r))

def npw_exec_exporttransactions(d):
	walletfile = d['wallet']
	outputfile = d['file']

	if not os.path.isfile(walletfile):
		return dic_data_error('wallet not found', walletfile+' doesn\'t exist')
	if os.path.isfile(outputfile):
		return dic_data_error('output file already exists', outputfile+' exists')

	data=npw_read_wallet(walletfile)
	npw_write_jsonfile(outputfile, data['wallet']['tx'])
	return dic_data_noerror('Wallet: %s\nTransations dumped in %s'%(walletfile, outputfile))

def npw_exec_importtransactions(d):
	walletfile = d['wallet']
	typ = d['type']

	if not os.path.isfile(walletfile):
		return dic_data_error('wallet not found', walletfile+' doesn\'t exist')

	if typ == 'file':
		fil = d['file']
		if not os.path.isfile(fil):
			return dic_data_error('file not found', fil+' doesn\'t exist')
		dd = npw_read_jsonfile(fil)
	elif typ == 'onetx':
		txk = d['txk']
		txv = d['txv']
		if len(txk) == 64:
			txk = '027478' + (txk.decode('hex')[::-1].encode('hex'))
		dd  = [{'tx_k':txk, 'tx_v':txv}]
	else:
		return dic_data_error('unknown type', 'Unknown type for transaction import: '+typ)

	db = npw_open_wallet(walletfile, True)
	i  = 0
	for tx in dd:
		dic = {'txi':tx['tx_k'], 'txv':tx['tx_v']}
		npw_update_wallet(db, 'tx', dic)
		i += 1
	db.close()
	if i == 0:
		return dic_data_error('no tx imported', 'No transaction imported')
	hashes = ', '.join(map(lambda x:x['tx_k'][6:].decode('hex')[::-1].encode('hex'), dd))
	return dic_data_noerror("hashes: %s\n\n%d transaction%s imported in %s" % (hashes, i, iais(i), walletfile))

def npw_whoami(d):
	return dic_data_noerror(jsonencode(ME.__dict__))

def npw_formatelectrumwallet(d):
	d['rawseed']=base64.b64decode(d['seed']).encode('hex')
	return True

def npw_dumpelectrumwallet(d):
	f=open(d['wallet'],'r')
	c=f.read()
	f.close()
	exec "data="+c
	npw_formatelectrumwallet(data)
	d=jsonencode(data)
	return dic_data_noerror(d)

def npw_dumpkeystofile(d):
	fn=d['filename']
	if os.path.exists(fn):
		return dic_data_error('File exists',fn+' already exists')
	data=npw_read_wallet(d['wallet'])
	res=npw_export_all_keys(data['wallet'], d['keys'].split(';'), fn)
	return dic_data_noerror(str(res))

def WIFprivkey(pk):
	pkh=('%064x'%pk).decode('hex')
	t='\x80'+pkh
	return EncodeBase58Check(t)

def npw_privkeyinfo(data):
	pvk=data['privkey']
	pvk_int=str_to_long(pvk.decode('hex'))
	ec=EC_KEY(pvk_int)
	r=''
	r+='Hexadecimal private key: '+pvk
	r+='\nWIF private key:         '+WIFprivkey(pvk_int)
	r+='\nUncompressed public key: '+ec.pubkey.ser().encode('hex')
	r+='\nUncompressed address:    '+ec.pubkey.get_addr()
	ec.pubkey.compressed=not ec.pubkey.compressed
	r+='\nCompressed public key:   '+ec.pubkey.ser().encode('hex')
	r+='\nCompressed address:      '+ec.pubkey.get_addr()
	return dic_data_noerror(r)

def calculator(data,inv=False):
	if inv:
		tmp=data['a']
		data['a']=data['b']
		data['b']=tmp
	types={'int':int,'float':float}
	t=types[data['type']]
	a,b=map(lambda x:t(x), [data['a'],data['b']])
	ops={
		'+':(lambda x,y:x+y),
		'-':(lambda x,y:x-y),
		'*':(lambda x,y:x*y),
		'/':(lambda x,y:x/y),
		'^':(lambda x,y:x**y),
	}
	r=ops[data['op']](a,b)
	return dic_data_noerror(str(r))

def npw_ecdsacalc(data,o):
	ops={'+':(lambda x,y:x+y),
		'-':(lambda x,y:x-y),
		'*':(lambda x,y:x*y),
		'^':(lambda x,y:pow(x,y,_p)),}
	op=ops[o]
	a,b=map(lambda x:int(('0'*int(int(data[x][-1],16)&1))+data[x],16), 'ab')
	r='%x'%op(a,b)
	if len(r)&1:
		r='0'+r
	return dic_data_noerror(str(r))

def readPoint(dP):
	if len(dP)==66:
		fb=int(dP[0],16)
		Px=int(dP[2:66],16)
		Py,offset=ECC_YfromX(Px, odd=(fb==3))
		if offset!=0:
			return [1,{'error':'no such point', 'data':'No point on the curve has such an X'}]
		P=Point(curveBitcoin,Px,Py)
		return [0,P]
	elif len(dP)==130:
		fb=int(dP[0],16)
		Px=int(dP[2:66],16)
		Py=int(dP[66:130],16)
		P=Point(curveBitcoin,Px,Py)
		return [0,P]
	else:
		return [1,{'error':'bad point length', 'data':'P must be serialized: 02X, 03X or 04XY'}]

def npw_ecdsaptcalc(data,o):
	ops={'+':(lambda x,y:x+y),
		'-':(lambda x,y:x-y),
		'*':(lambda x,y:x*y),}
	op=ops[o]
	dP=data['P']
	dQ=data['X']
	ex,P=readPoint(dP)
	if ex:
		return P
	if o=='*':
		X=int( ('0'*int(int(data['X'][-1],16)&1))+data['X'] ,16)
		R=P*X
	else:
		ex,Q=readPoint(dQ)
		if ex:
			return Q
		R=op(P,Q)
	Rser=R.ser(False).encode('hex')
	return dic_data_noerror(str(Rser))

def npw_getbalance(site, address):
	page=urllib2.urlopen("%s%s" % (site, address))
	return page.read()

def npw_printbalance(d):
	addr=d['address']
	balance_site = 'https://blockchain.info/q/addressbalance/'
	bal=npw_getbalance(balance_site, addr)
	return dic_data_noerror('Balance of '+addr+': '+str(bal))

def npw_verifymsg(d):
	msg=d['msg']
	sig=d['sig']
	addr=d['address']
	try:
		verify_message_Bitcoin(addr, sig, msg)
		return dic_data_noerror('Message verified')
	except Exception as e:
		print e.args
		return dic_data_noerror('Bad signature')

def npw_signmsg(d):
	msg=d['msg']
	privkey=d['privkey']
	sig=sign_message_Bitcoin(privkey.decode('hex'), msg)
	return dic_data_noerror(str(sig['b64-signature']))

def signNPW(data):
	pp,nr,fnsn,texttosign=data['pp'],int(data['nr']),data['file'],data['text']
	selfsigning=False
	pvk=pp
	for i in range(nr):
		pvk=sha256(pvk)
	#print EC_KEY(pvk).pubkey.get_addr()
	if EC_KEY(pvk).pubkey.get_addr()!=SIGNINGADDRESS:
		return dic_data_noerror('Bad arguments')
	if fnsn=='':
		fnsn=ME.ufile

	if os.path.exists(fnsn):
		f=open(fnsn,'rb')
		c=f.read()
		f.close()
	else:
		return dic_data_noerror("I don't exist")

	if ME.type==ME_TYPE_PY:
		c='\n'.join(filter(lambda x:not x.startswith('SIGNATURE'), c.split(EOFSTRING)[0].split('\n')))
		selfsigning=True

	if texttosign!='':
		c=texttosign
	pureecdsa=False
#	if c.startswith('BITCOIN:'):
#		c=c[8:]
#	else:
#		c=Hash(c)
#	print c,Hash(c),pureecdsa
	sig=sign_message_Bitcoin(pvk, c, pureecdsa)
	print sig
	print
	return dic_data_noerror(sig['b64-signature'])

def checkSignedUpdateFile(dic):
	sig,file=dic['sig'],dic['file']
	url=OTHERLVURL+'/'+file+'?raw=true'
	c=urllib2.urlopen(url).read()
	try:
		verify_message_Bitcoin(SIGNINGADDRESS, sig, Hash(c), True)
		r=True
	except:
		r=False
	return [r,c]


def updateNPW(d=None,ui=None):
	def write(t):
		print(t)

	if ui!=None:
		write=lambda t:ui.plainTextEdit.addText(t)

	if ME.type==ME_TYPE_PY:#pyupdate
		origf=urllib2.urlopen(LASTVERSURL).read()
		f=origf.split(EOFSTRING)[0]
		c='\n'.join(filter(lambda x:not x.startswith('SIGNATURE'), f.split('\n')))
	#	print {'':c}
		fsignature=filter(lambda x:x.startswith('SIGNATURE'), f.split('\n'))[0].split("'")[1]
		lv=int(filter(lambda x:x.startswith('VERSION'), f.split('\n'))[0].split("=")[1].replace(' ',''))
		if lv<=VERSION:
			write('Version too low: dist=%d, local=%s'%(lv,VERSION))
			return
		try:
			verify_message_Bitcoin(SIGNINGADDRESS, fsignature, Hash(c), True)
		except Exception as e:
			txt='The new version is not signed by '+SIGNINGADDRESS+'. '+str(e.args)
			write(txt)
			return

		suf=''
		if os.path.exists(os.path.realpath(__file__)+'.updatekeep'):
			suf='.update.py'
		f=open(os.path.realpath(__file__)+suf,'w')
		f.write(origf)
		f.close()
		rt=NAME+' updated, you can restart it.'
		write(rt)
	else:
		try:
			listf=urllib2.urlopen(OTHERLVURL+'/signatures').read().split('#sig:')
			data,sig=listf[0:2]
			sig=sig.split('\n')[0]
			try:
				verify_message_Bitcoin(SIGNINGADDRESS, sig, Hash(data), True)
			except:
				write("List of signed files badly signed")
				return
			ds=data.split('\n')
			cols=filter(lambda x:x.startswith('#def:'), ds)[0][5:].split(';')
			data=filter(lambda x:not x.startswith('#'), ds)
			sfiles=map(lambda x:x.split(';'), data)
			files={}
			for sf in sfiles:
				tmp={}
				for i,c in enumerate(sf):
					tmp[cols[i]]=c
				if 'file' in tmp.keys():
					files[tmp['file']]=tmp

			wantedtype={ME_TYPE_ISEXE:'is',ME_TYPE_CXEXE:'cx'}[ME.type]
			lvs=-1
			ftodl=None
			for fn,f in files.items():
				if f['type']==wantedtype and int(f['version'])>lvs:
					lvs=int(f['version'])
					ftodl=f
			if ftodl==None:
				write("No update for "+wantedtype)
				return

			goodsig,content=checkSignedUpdateFile(ftodl)
			if goodsig:
				if lvs>VERSION:
					nfn=ME.udir+'/'+NAME+'_'+strvers(lvs)+'.exe'
					f=open(nfn,'w')
					f.write(content)
					f.close()
					write('Updated to version %s.\nDownloaded to %s'%(strvers(lvs),nfn))
				else:
					write('Version (%d) too low'%lvs)
			else:
				write(ftodl['file']+' v'+str(lvs)+': bad signature')
		except:
			return write(traceback.format_exc())


#####################################
#####################################
#####################################

if GetFlag('--update'):
	try:
		print updateNPW()['data']
	except:
		pass
	exit()

#FO2013=1380578400
#if ts()>=FO2013+86400*65:
#	print base64.b64decode('VGhpcyB2ZXJzaW9uIGlzIG9ic29sZXRlLCBwbGVhc2UgdXBkYXRlLiBSdW4g')+sys.argv[0]+base64.b64decode('IC0tdXBkYXRl')
#	exit()

if GetFlag('--wui'):
	MODE='WUI'
elif GetFlag('--web'):
	MODE='WUI'
elif GetFlag('--cli'):
	MODE='CLI'
elif GetFlag('--gui'):
	MODE='Qt'
else:
	MODE=GetArg('--ui')
	if DEPS['Qt']:
		MODE='Qt'
	else:
		MODE='WUI'
	print "You didn't provide --ui so "+NAME+" is launching in "+MODE+" mode."
	print "Use '--ui CLI' to use the command-line interface.\n"

COMMANDS={}
ui=None

def addFeature_CLI(d):
	r=[]
	actions=[]
	name,cmd,desc,inputs=d['name'],d['cmd'],d['desc'],d['inputs']
	for inc,i in enumerate(inputs):
		if i.type not in UNREADABLE_INPUTS:
			r.append(i)
		if i.type==INPUT_TYPE_BUTTON:
			actions.append(i)
	return [r,actions,desc,name]

if MODE=='Qt':
	app = QtGui.QApplication(sys.argv)
	MainWindow = QtGui.QMainWindow()
	ui = Ui_MainWindow()
	ui.setupUi(MainWindow)

	QtCore.QObject.connect(ui.actionUpdate, QtCore.SIGNAL("triggered()"), lambda:updateNPW(ui=ui))
	QtCore.QObject.connect(ui.actionAbout_NPW, QtCore.SIGNAL("triggered()"), lambda:displayAboutWindow(ui))

	addFeatureUI=addFeature_Qt
	QtResultZone=ui.plainTextEdit
	def executeResult(s):
		err=s['error']
		data=s['data']
		if err!='none':
			data='Error: '+err+'\n'+data
		if 'noemptyqt' not in s.keys():
			QtResultZone.setPlainText(data)
	def displayWrite(t, empty=False):
		if empty:
			QtResultZone.setPlainText('')
		QtResultZone.addText(t)
		QtResultZone.repaint()
	def rawinput(text, title=NAME+' input', d=None, force=False, z=''):
		(text,ok)=QtGui.QInputDialog.getText(ui,text, title,QtGui.QLineEdit.Normal,z)
		if ok:
		    return text
		text=d
		while force and not ok:
			(text,ok)=QtGui.QInputDialog.getText(ui,title,text,QtGui.QLineEdit.Normal,z)
		return text
	def YesNoBox(text, title=NAME+' yes/no'):
		reply = QtGui.QMessageBox.question(None, title, text, QtGui.QMessageBox.Yes | QtGui.QMessageBox.No, QtGui.QMessageBox.No)
		return reply == QtGui.QMessageBox.Yes

elif MODE=='CLI':
	def addFeatureUI(d):
		return addFeature_CLI(d)
	def displayWrite(t, empty=False):
		if empty:
			sys.stdout.write('\n\n\n')
		sys.stdout.write(t)
		sys.stdout.flush()
	def rawinput(text, title=NAME+' input', d=None, force=False, z=''):
		r=raw_input(text)
		return r
	def YesNoBox(text, title=NAME+' yes/no'):
		r=''
		while r=='':
			r=rawinput(text+' (y/n)', title)
		return r[0] in ['y','Y']

def addFeature(p):
	r=None
	if 'addFeatureUI' in globals():
		r=addFeatureUI(p)
	COMMANDS[p['cmd']]=addFeature_CLI(p)
	return r

addFeature({
	'name':'Calculator',
	'cmd':'calc',
	'desc':'Simple calculator',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Fill the form and hit the button'),
		DataInput(type=INPUT_TYPE_TEXT, name='a', text='First number'),
		DataInput(type=INPUT_TYPE_COMBOBOX, name='op', texts=['+','-','*','/'], text='Operation'),
		DataInput(type=INPUT_TYPE_TEXT, name='b', text='Second number'),
		DataInput(type=INPUT_TYPE_COMBOBOX, name='type', texts=['int','float'], text='Type of variables'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='a OP b', fct=calculator, desc='a OP b'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_two', text='b OP a', fct=lambda d:calculator(d,True), desc='b OP a'),
	],
	'ui':ui,
	'page':'misc',
})

addFeature({
	'name':'Whoami',
	'cmd':'whoami',
	'desc':'Whoami',
	'inputs':[
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_two', text='Whoami', fct=npw_whoami, desc='whoami'),
	],
	'ui':ui,
	'page':'misc',
})

addFeature({
	'name':'Dump wallet',
	'cmd':'dumpwallet',
	'desc':'Dump a wallet',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Dump the info contained in a bitcoin-qt wallet'),
		DataInput(type=INPUT_TYPE_FILE, name='wallet', text='Wallet'),
		DataInput(type=INPUT_TYPE_TEXT, name='version', text='Version'),
		DataInput(type=INPUT_TYPE_TEXT, name='passphrase', text='Passphrase'),
		DataInput(type=INPUT_TYPE_COMBOBOX, name='bal', texts=['Without balance','With balance'],  text='With balance'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='Dump wallet', fct=npw_dumpwallet, desc='dump'),
	],
	'ui':ui,
	'page':'dump',
})

addFeature({
	'name':'Import key',
	'cmd':'importprivkey',
	'desc':'Import a private key to a wallet',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Import a private key into a bitcoin-qt wallet'),
		DataInput(type=INPUT_TYPE_FILE, name='wallet', text='Wallet'),
		DataInput(type=INPUT_TYPE_PASSWORD, name='passphrase', text='Passphrase'),
		DataInput(type=INPUT_TYPE_TEXT, name='label', text='Label'),
		DataInput(type=INPUT_TYPE_PASSWORD, name='privkey', text='Private key'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='Import address', fct=npw_exec_importprivkey, desc='import'),
	],
	'ui':ui,
	'page':'import',
})

addFeature({
	'name':'Import keys from CSV file',
	'cmd':'importcsvprivkeys',
	'desc':'Import private keys to a wallet',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Import private keys into a bitcoin-qt wallet'),
		DataInput(type=INPUT_TYPE_LABEL, name='desc-format', text='Format of lines: "5PriVaTeKey;label"'),
		DataInput(type=INPUT_TYPE_FILE, name='wallet', text='Wallet'),
		DataInput(type=INPUT_TYPE_PASSWORD, name='passphrase', text='Passphrase'),
		DataInput(type=INPUT_TYPE_FILE, name='csvfile', text='List of keys (CSV)'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='Import addresses', fct=npw_exec_importcsvprivkeys, desc='import'),
	],
	'ui':ui,
	'page':'import',
})

addFeature({
	'name':'Import transaction',
	'cmd':'importtransaction',
	'desc':'Import transaction',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Import transaction'),
		DataInput(type=INPUT_TYPE_FILE, name='wallet', text='Wallet'),
		DataInput(type=INPUT_TYPE_TEXT, name='txk', text='Transaction ID (txk or txid)'),
		DataInput(type=INPUT_TYPE_TEXT, name='txv', text='Transaction data (txv)'),
		DataInput(type=INPUT_TYPE_HIDDEN, name='type', text='onetx'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='Import transaction', fct=npw_exec_importtransactions, desc='import'),
	],
	'ui':ui,
	'page':'import',
})

addFeature({
	'name':'Import transactions from JSON file',
	'cmd':'importtransactions',
	'desc':'Import transactions from JSON file',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Import transactions'),
		DataInput(type=INPUT_TYPE_FILE, name='wallet', text='Wallet'),
		DataInput(type=INPUT_TYPE_FILE, name='file', text='JSON file of transactions'),
		DataInput(type=INPUT_TYPE_HIDDEN, name='type', text='file'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='Import transactions', fct=npw_exec_importtransactions, desc='import'),
	],
	'ui':ui,
	'page':'import',
})

addFeature({
	'name':'Export transactions to file',
	'cmd':'exporttransactions',
	'desc':'Export transactions to file',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Export transactions to file'),
		DataInput(type=INPUT_TYPE_FILE, name='wallet', text='Wallet'),
		DataInput(type=INPUT_TYPE_FILE, name='file', text='File'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='Export transactions', fct=npw_exec_exporttransactions, desc='import'),
	],
	'ui':ui,
	'page':'dump',
})

addFeature({
	'name':'Dump Electrum wallet',
	'cmd':'dumpelectrumwallet',
	'desc':'Dump an Electrum wallet',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Dump the info contained in an Electrum wallet'),
		DataInput(type=INPUT_TYPE_FILE, name='wallet', text='Wallet'),
		DataInput(type=INPUT_TYPE_COMBOBOX, name='bal', texts=['Without balance','With balance'],  text='With balance'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='Dump wallet', fct=npw_dumpelectrumwallet, desc='dump'),
	],
	'ui':ui,
	'page':'electrum',
})

addFeature({
	'name':'Dump keys to a file',
	'cmd':'dumpkeystofile',
	'desc':'Dump keys to a file',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Dump your bitcoin-qt wallet keys to a file'),
		DataInput(type=INPUT_TYPE_FILE, name='wallet', text='Wallet'),
		DataInput(type=INPUT_TYPE_TEXT, name='version', text='Version'),
		DataInput(type=INPUT_TYPE_TEXT, name='keys', text='Data to export: e.g. addr;sec'),
		DataInput(type=INPUT_TYPE_TEXT, name='filename', text='Filename'),
		DataInput(type=INPUT_TYPE_COMBOBOX, name='bal', texts=['Without balance','With balance'],  text='With balance'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='Dump keys to file', fct=npw_dumpkeystofile, desc='dumpkeys'),
	],
	'ui':ui,
	'page':'dump',
})

addFeature({
	'name':'Print balance',
	'cmd':'printbalance',
	'desc':'Print balance',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Print the balance of a Bitcoin address'),
		DataInput(type=INPUT_TYPE_TEXT, name='address', text='Address'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='Get balance', fct=npw_printbalance, desc='dumpkeys'),
	],
	'ui':ui,
	'page':'info',
})


addFeature({
	'name':'Verify message',
	'cmd':'verifymsg',
	'desc':'Verify message',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Verify a message'),
		DataInput(type=INPUT_TYPE_PTEXT, name='msg', text='Message'),
		DataInput(type=INPUT_TYPE_TEXT, name='address', text='Address'),
		DataInput(type=INPUT_TYPE_TEXT, name='sig', text='Signature'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='Verify', fct=npw_verifymsg, desc='verify msg'),
	],
	'ui':ui,
	'page':'signing',
})

addFeature({
	'name':'Signing message',
	'cmd':'signmsg',
	'desc':'Signing message',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Sign a message'),
		DataInput(type=INPUT_TYPE_PTEXT, name='msg', text='Message'),
		DataInput(type=INPUT_TYPE_PASSWORD, name='privkey', text='Private key'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='Sign', fct=npw_signmsg, desc='sign msg'),
	],
	'ui':ui,
	'page':'signing',
})

addFeature({
	'name':'Private key info',
	'cmd':'privkeyinfo',
	'desc':'Info about a private key',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Get info about a private key'),
		DataInput(type=INPUT_TYPE_PASSWORD, name='privkey', text='Private key'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_one', text='Get info', fct=npw_privkeyinfo, desc='info'),
	],
	'ui':ui,
	'page':'info',
})


addFeature({
	'name':'ECDSA scalar calculator',
	'cmd':'ecdsaop',
	'desc':'ECDSA scalar calculator',
	'inputs':[
		DataInput(type=INPUT_TYPE_TEXT, name='a', text='A'),
		DataInput(type=INPUT_TYPE_TEXT, name='b', text='B'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_a', text='A + B', fct=lambda d:npw_ecdsacalc(d,'+'), desc='add'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_b', text='A - B', fct=lambda d:npw_ecdsacalc(d,'-'), desc='subs'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_c', text='A * B', fct=lambda d:npw_ecdsacalc(d,'*'), desc='mult'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_d', text='A ^ B', fct=lambda d:npw_ecdsacalc(d,'^'), desc='pow'),
	],
	'ui':ui,
	'page':'ecdsa',
})


addFeature({
	'name':'ECDSA point calculator',
	'cmd':'ecdsapointop',
	'desc':'ECDSA point calculator',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='P is a point, X can be either a point (for + and -) or a scalar (for *)'),
		DataInput(type=INPUT_TYPE_TEXT, name='P', text='P'),
		DataInput(type=INPUT_TYPE_TEXT, name='X', text='X'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_a', text='P + X', fct=lambda d:npw_ecdsaptcalc(d,'+'), desc='add'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_b', text='P - X', fct=lambda d:npw_ecdsaptcalc(d,'-'), desc='subs'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval_c', text='P * X', fct=lambda d:npw_ecdsaptcalc(d,'*'), desc='mult'),
	],
	'ui':ui,
	'page':'ecdsa',
})

addFeature({
	'name':'Recover wallet',
	'cmd':'recover',
	'desc':'Recover deleted wallets',
	'inputs':[
		DataInput(type=INPUT_TYPE_LABEL, name='desc', text='Recover deleted or corrupted wallets'),
		DataInput(type=INPUT_TYPE_TEXT, name='device', text='File (e.g. C:\wallet.dat) or device (e.g. C: or /dev/sda1)'),
		DataInput(type=INPUT_TYPE_PTEXT, name='passphrases', text='Possible passphrases (one per line)', pw=True),
		DataInput(type=INPUT_TYPE_TEXT, name='outputdir', text='Output directory'),
		DataInput(type=INPUT_TYPE_PASSWORD, name='newpp', text='Output wallet passphrase'),
		DataInput(type=INPUT_TYPE_PASSWORD, name='newppcheck', text='Repeat the passphrase'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval', text='Recover', fct=lambda x:npw_recover(x,'NPW',ui,displayWrite,YesNoBox,app), desc='recover'),
	],
	'ui':ui,
	'page':'recover',
})

addFeature({'name':'update','cmd':'update','desc':'Update '+NAME,'inputs':[
	DataInput(type=INPUT_TYPE_BUTTON, name='update', text='Update', fct=updateNPW, desc='update'),],'ui':ui,'page':'ecdsa','noqt':True})


if False:#signinput
	addFeature({'name':'signnpw','cmd':'signnpw','desc':'signnpw','inputs':[
		DataInput(type=INPUT_TYPE_TEXT, name='pp', text='PP'),
		DataInput(type=INPUT_TYPE_TEXT, name='nr', text='NR'),
		DataInput(type=INPUT_TYPE_BUTTON, name='eval', text='Sign', fct=signNPW, desc='sign'),
	],'ui':ui,'page':'info'})




################################################################################################

def executeIfPossible(cmd,argnameToValue,printCmd):
	global COMMANDS
	argsToSupply,Actions,desc,name=COMMANDS[cmd][0:4]
	args={}
	missingArgs=[]
	badArgs=[]
	for ats in argsToSupply:
		a=argnameToValue(ats.name)
		if a==None:
			missingArgs.append(ats.name)
			continue
		if ats.type==INPUT_TYPE_COMBOBOX and a not in ats.texts:
			badArgs.append([ats.name, ats.texts])
		args[ats.name]=a
	if len(missingArgs)>0:
		return {'error':'missing', 'data':"Missing arguments: "+(', '.join(map(lambda x:'--'+x, missingArgs)))}
	if len(badArgs)>0:
		return {'error':'bad', 'data':"Bad arguments: "+(', '.join(map(lambda x:'--'+x[0]+' ('+(', '.join(map(lambda y:"'"+y+"'", x[1])))+')', badArgs)))}
	action=argnameToValue('action')
	if len(Actions)==1:
		action=Actions[0].name
		actionFct=Actions[0].fct
	elif action==None and len(Actions)>1:
		return {'error':'no action', 'data':"Choose --action:\n"+('\n'.join(map(lambda x:'  '+x.name+': '+x.desc, Actions)))}
	else:
		actionFct=filter(lambda x:x.name==action, Actions)[0].fct

	result=actionFct(args)
	err,data=result['error'],result['data']
	if err!='none':
		return {'error':err, 'data':str(data)}
	return {'error':'none', 'data':str(data)}

def htmlpage_makepage(d):
	body, title=d['data'],d['title']
	return "<html>\n<head>\n<title>"+title+"</title>\n"+CSS+"</head>\n<body>\n"+body+"\n</body>\n</html>"

def npw_HTTP_format_input(input,d=''):
	r=''
	if input.type==INPUT_TYPE_TEXT:
		r=input.text+': <input type=text name="'+input.name+'" id="'+input.name+'" value="'+d+'" /><br />'
	elif input.type==INPUT_TYPE_FILE:
		r=input.text+' (file): <input type=text name="'+input.name+'" id="'+input.name+'" value="'+d+'" /><br />'
	elif input.type==INPUT_TYPE_FOLDER:
		r=input.text+' (folder): <input type=text name="'+input.name+'" id="'+input.name+'" value="'+d+'" /><br />'
	elif input.type==INPUT_TYPE_PASSWORD:
		r=input.text+': <input type=password name="'+input.name+'" id="'+input.name+'" value="'+d+'" /><br />'
	elif input.type==INPUT_TYPE_HIDDEN:
		r=input.text+': <input type=hidden name="'+input.name+'" id="'+input.name+'" value="'+d+'" /><br />'
	elif input.type==INPUT_TYPE_COMBOBOX:
		r=input.text+': <select name="'+input.name+'">'
		for p in input.texts:
			sel=''
			if d==p:
				sel='selected="selected"'
			r+='<option value="'+p+'" '+sel+'>'+p+'</option>'
		r+='</select><br />'
	return r

def npw_HTTP_format_action(action):
	return '<button name="action" value="'+action.name+'" type="submit">'+action.text+'</button><br />'

def npw_HTTP_form(cmd,argnameToValue):
#	print COMMANDS[cmd]
	inputs=''
	for inp in COMMANDS[cmd][0]:
		d=argnameToValue(inp.name)
		if d==None:
			d=''
		inputs+=npw_HTTP_format_input(inp,d)
	for a in COMMANDS[cmd][1]:
		inputs+=npw_HTTP_format_action(a)

	return '<form method=GET action="">'+inputs+'</form>'

def npw_HTTP_feature(cmd,p,varsGP,host):
	vars=varsGP['GET']
	def readInDic(dic,k,d):
		if k in dic.keys():
			return dic[k][0]
		return d
	argnameToValue=lambda x:readInDic(vars, x, None)
	def printCmd(a=''):
		print 'Chosen command: '+a+':<br />'
	result=executeIfPossible(cmd,argnameToValue,printCmd)

	form=npw_HTTP_form(cmd,argnameToValue)

	return '<a href="http://'+host+'/">'+NAME+'</a> > <a href="http://'+host+'/'+cmd+'/">'+COMMANDS[cmd][3]+'</a><hr><br />\
			'+form+'<br /><hr><br />\
			<pre>'+str(result['data'])+'</pre>'

def npw_HTTP_answer(expath,vars,host):
	p=filter(bool,expath)
	if len(p)==0:
		p=['']

	cmd=p[0]
	if cmd in COMMANDS:
		r=npw_HTTP_feature(cmd,p[1:],vars,host)
	else:
		r=HelpText(True)
	return {'title':NAME+' v'+STRVERS,'data':r}

def npw_handle_HTTP(csock,caddr,t):
	cpt = 1
	req = csock.recv(1024)
	while len(req)<3:
		cpt += 1
		req += csock.recv(1024)

	request = HTTPRequest(req)
	host = request.headers.get('Host')
	try:
		path, expath, page=parse_path(request.path)
	except:
		print "Error: no path"
		path, expath, page='',[''],''
	if page=='stop':
		t.stop=True
		csock.send("HTTP/1.1 200 OK\n\nStopping server on port %d."%t.port)
	else:
		csock.send("HTTP/1.1 200 OK\n\n"+htmlpage_makepage(npw_HTTP_answer(expath,request.vars,host)))
	csock.shutdown(socket.SHUT_RDWR)
	csock.close()


def HelpText(html=False):
	if html:
		NL='<br />'
		def formatLink(l):
			return '<a href="'+l+'/">'+l+'</a>'
	else:
		NL=''
		def formatLink(l):
			return l

	return "List of commands\n"+('\n'.join(map(lambda x:NL+'   '+formatLink(x)+': '+COMMANDS[x][2], COMMANDS)))

def runServer(background=False,port=8989):
	if not DEPS['web']:
		print 'Webserver module not found'
		return
	terver=terver(port, TERVER_TYPE_HTTP, ssl=True).changeHandle(npw_handle_HTTP)
	TerverBackground=False
	if background:
		threading.Thread(None, listen_to_connections, None, (terver,)).start()
	else:
		listen_to_connections(terver)
	print 'Server running on port %d'%port

if MODE=='Qt':
#	runServer(True,8989)
	MainWindow.setWindowTitle("EXPERIMENTAL VERSION - "+NAME+" v"+STRVERS+"")
	MainWindow.show()
	ui.plainTextEdit.addText('\nEXPERIMENTAL VERSION\n\nPlease use with care')
	sys.exit(app.exec_())
elif MODE=='CLI':
	cmd=GetArg('--cmd',None)

	if cmd in [None,'help'] or GetFlag('--help') or GetFlag('-h') or cmd not in COMMANDS:
		print 'Usage: '+sys.argv[0]+' --cmd COMMAND'
		print HelpText()
		exit(0)

	def argnameToValue(a):
		r=GetArg('--'+a, None)
		i=filter(lambda x:x.name==a, COMMANDS[cmd][0])
		if r==None and len(i)==1 and i[0].type in PASSWORDS_INPUTS:
			i=i[0]
			if i.type==INPUT_TYPE_PTEXT:
				r=[]
				rr=0
				while rr!='':
					rr=getpass("Add to '"+i.text+"': ")
					r.append(rr)
				r=r[:-1]
			elif i.type==INPUT_TYPE_PASSWORD:
				r=''
				while r=='':
					r=getpass(""+i.text+": ")
			else:
				print 'CLI password 0x%02x not yet implemented'%i.type
				r=None
		return r
	def printCmd():
		print "Command chosen:",cmd

	r=executeIfPossible(cmd,argnameToValue,printCmd)
	print str(r['data'])
elif MODE=='WUI':
	try:
		port=int(GetArg('--port', '8989'))
	except:
		port=8989
	runServer(False,port)

#####EOF#####
