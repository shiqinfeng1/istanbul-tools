// Copyright 2017 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.
// 编译选项：在 nacl 或 js 或 nocgo 并且是 kquorum 时编译

package crypto

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/ecdsa"
	"crypto/sha512"
	"crypto/rand"
	"crypto/elliptic"
	// "encoding/hex"
	"io"
	"errors"
	"fmt"
	"math/big"
)

const (
	pubkeyCompressed   byte = 0x2 // y_bit + x coord
	pubkeyUncompressed byte = 0x4 // x coord + y coord
	pubkeyHybrid       byte = 0x6 // y_bit + x coord + y coord
	
	PubKeyBytesLenCompressed   = 33
	PubKeyBytesLenUncompressed = 65
	PubKeyBytesLenHybrid       = 65

	aesIV = "IV for <SM2> CTR"
	
)

var one = new(big.Int).SetInt64(1)

// Signature is a type representing an ecdsa signature.
type Signature struct {
	R *big.Int
	S *big.Int
}
type zr struct {
	io.Reader
}

func (z *zr) Read(dst []byte) (n int, err error) {
	for i := range dst {
		dst[i] = 0
	}
	return len(dst), nil
}
var zeroReader = &zr{}

func getLastBit(a *big.Int) uint {
	return a.Bit(0)
}
func isOdd(a *big.Int) bool {
	return a.Bit(0) == 1
}
// 32byte
func zeroByteSlice() []byte {
	return []byte{
		0, 0, 0, 0,
		0, 0, 0, 0,
		0, 0, 0, 0,
		0, 0, 0, 0,
		0, 0, 0, 0,
		0, 0, 0, 0,
		0, 0, 0, 0,
		0, 0, 0, 0,
	}
}
// paddedAppend appends the src byte slice to dst, returning the new slice.
// If the length of the source is smaller than the passed size, leading zero
// bytes are appended to the dst slice before appending src.
func paddedAppend(size uint, dst, src []byte) []byte {
	for i := 0; i < int(size)-len(src); i++ {
		dst = append(dst, 0)
	}
	return append(dst, src...)
}

func randFieldElement(c elliptic.Curve, rand io.Reader) (k *big.Int, err error) {
	params := c.Params()
	b := make([]byte, params.BitSize/8+8)
	_, err = io.ReadFull(rand, b)
	if err != nil {
		return
	}
	k = new(big.Int).SetBytes(b)
	n := new(big.Int).Sub(params.N, one)
	k.Mod(k, n)
	k.Add(k, one)
	return
}

// Sign calculates an ECDSA signature.
//
// This function is susceptible to chosen plaintext attacks that can leak
// information about the private key that is used for signing. Callers must
// be aware that the given hash cannot be chosen by an adversery. Common
// solution is to hash any input before calculating the signature.
//
// The produced signature is in the [R || S || V] format where V is 0 or 1.
func Sign(hash []byte, priv *ecdsa.PrivateKey) ([]byte, error) {

	var r, s *big.Int
	// var y *big.Int
	if len(hash) != 32 {
		return nil, fmt.Errorf("hash is required to be exactly 32 bytes (%d)", len(hash))
	}
	if priv.Curve != P256Sm2() {
		return nil, fmt.Errorf("private key curve is not P256-Sm2")
	}
	entropylen := (priv.Curve.Params().BitSize + 7) / 16
	if entropylen > 32 {
		entropylen = 32
	}
	entropy := make([]byte, entropylen)
	_, err := io.ReadFull(rand.Reader, entropy)  // 生成一个随机熵
	if err != nil {
		return  nil, fmt.Errorf("generate entropy fail")
	}

	// Initialize an SHA-512 hash context; digest ...
	// 计算hash512(priv.D | entropy | hash) 并取前32字节
	md := sha512.New()
	md.Write(priv.D.Bytes()) // the private key,
	md.Write(entropy)        // the entropy,
	md.Write(hash)           // and the input hash;
	key := md.Sum(nil)[:32]  // and compute ChopMD-256(SHA-512),
	// which is an indifferentiable MAC.
	// Create an AES-CTR instance to use as a CSPRNG.
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, err
	}
	// Create a CSPRNG that xors a stream of zeros with
	// the output of the AES-CTR instance.
	csprng := cipher.StreamReader{
		R: zeroReader,
		S: cipher.NewCTR(block, []byte(aesIV)),
	}

	// See [NSA] 3.4.1
	c := priv.PublicKey.Curve
	N := c.Params().N
	if N.Sign() == 0 {
		return nil, fmt.Errorf("zero parameter")
	}
	var k *big.Int
	e := new(big.Int).SetBytes(hash)
	for { 
		for {
			k, err = randFieldElement(c, csprng)  // 生产成一个临时私钥
			if err != nil {
				r = nil
				return nil, fmt.Errorf("create a CSPRNG fail")
			}
			r, _ = priv.Curve.ScalarBaseMult(k.Bytes())
			// r, y = priv.Curve.ScalarBaseMult(k.Bytes())  // 生成一个临时公钥,r是x坐标：x1
			r.Add(r, e)   // r = x1 + e
			r.Mod(r, N)   // r = （x1 + e）mod N
			// 若r=0或r+k=n则需要重新生成k。
			if r.Sign() != 0 {  //判断t = r + k 是否等于0
				if t := new(big.Int).Add(r, k); t.Cmp(N) != 0 {  //判断t = r + k 是否等于N
					break
				}
			}
		}
		rD := new(big.Int).Mul(priv.D, r)  // rD = priv.D * (r)
		s = new(big.Int).Sub(k, rD)     // s = k -  priv.D * (r) 
		d1 := new(big.Int).Add(priv.D, one) 
		d1Inv := new(big.Int).ModInverse(d1, N)
		s.Mul(s, d1Inv)    // s = (k -  priv.D * r) /(priv.D + 1) mod N
		s.Mod(s, N)
		if s.Sign() != 0 {
			break
		}
	}
	// e = H256(M')
	// r=(e + x1) mod n
	// s = ((k − r * dA) / (1 + dA)) mod n

	// 将r,s组装成[]byte
	// bitcoind checks the bit length of R and S here. The ecdsa signature
	// algorithm returns R and S mod N therefore they will be the bitsize of
	// the curve, and thus correctly sized.
	sig := &Signature{R: r, S: s}
	for i := 0; i < (P256Sm2().H+1)*2; i++ {
		pk, err := recoverKeyFromSignature(P256Sm2(), sig, hash, i, true)
		if err == nil && pk.X.Cmp(priv.X) == 0 && pk.Y.Cmp(priv.Y) == 0 {
			result := make([]byte, 1, 2*P256Sm2().byteSize+1)
			result[0] = 27 + byte(i)
			// if isCompressedKey {
			// 	result[0] += 4
			// }
			// Not sure this needs rounding but safer to do so.
			curvelen := (P256Sm2().BitSize + 7) / 8

			// 不足长度的先追加0，补足长度。
			// Pad R and S to curvelen if needed.
			bytelen := (sig.R.BitLen() + 7) / 8
			if bytelen < curvelen {
				result = append(result, make([]byte, curvelen-bytelen)...)
			}
			result = append(result, sig.R.Bytes()...)

			bytelen = (sig.S.BitLen() + 7) / 8
			if bytelen < curvelen {
				result = append(result, make([]byte, curvelen-bytelen)...)
			}
			result = append(result, sig.S.Bytes()...)

			// Convert to Ethereum signature format with 'recovery id' v at the end.
			v := result[0] - 27
			copy(result, result[1:])
			result[64] = v
			return result, nil
		}
	}
	return nil, fmt.Errorf("sign fail. r:%v, s:%v", r, s)
}

func parsePubKey(pubKeyStr []byte, curve *Sm2P256Curve) (key *ecdsa.PublicKey, err error) {
	pubkey := &ecdsa.PublicKey{}
	pubkey.Curve = curve

	if len(pubKeyStr) == 0 {
		return nil, errors.New("pubkey string is empty")
	}

	format := pubKeyStr[0]
	ybit := (format & 0x1) == 0x1
	format &= ^byte(0x1)

	switch len(pubKeyStr) {
	case PubKeyBytesLenUncompressed:
		if format != pubkeyUncompressed && format != pubkeyHybrid {
			return nil, fmt.Errorf("invalid magic in pubkey str: %d", pubKeyStr[0])
		}

		pubkey.X = new(big.Int).SetBytes(pubKeyStr[1:33])
		pubkey.Y = new(big.Int).SetBytes(pubKeyStr[33:])
		// hybrid keys have extra information, make use of it.
		if format == pubkeyHybrid && ybit != isOdd(pubkey.Y) {
			return nil, fmt.Errorf("ybit doesn't match oddness")
		}
	case PubKeyBytesLenCompressed:
		pubkey,err = DecompressPubkey(pubKeyStr)
		if err != nil {
			return nil, err
		}
	default: // wrong!
		return nil, fmt.Errorf("invalid pub key length %d",
			len(pubKeyStr))
	}

	if pubkey.X.Cmp(pubkey.Curve.Params().P) >= 0 {
		return nil, fmt.Errorf("Parse PubKey pubkey X parameter is >= to P")
	}
	if pubkey.Y.Cmp(pubkey.Curve.Params().P) >= 0 {
		return nil, fmt.Errorf("Parse PubKey pubkey Y parameter is >= to P")
	}
	if !pubkey.Curve.IsOnCurve(pubkey.X, pubkey.Y) {
		return nil, fmt.Errorf("Parse PubKey pubkey isn't on secp256k1 curve")
	}
	return pubkey, nil
}
// VerifySignature checks that the given public key created signature over hash.
// 公钥可以是压缩公钥 (33 bytes)或非压缩公钥(65 bytes).
// 签名的格式是 64 byte [R || S] format.
func VerifySignature(pubkey, hash, signature []byte) bool {

	if len(signature) != 64 {
		return false
	}
	r := new(big.Int).SetBytes(signature[:32])
	s := new(big.Int).SetBytes(signature[32:])

	pub, err := parsePubKey(pubkey, P256Sm2())
	if err != nil {
		return false
	}
	c := pub.Curve
	N := c.Params().N

	if r.Sign() <= 0 || s.Sign() <= 0 {
		return false
	}
	if r.Cmp(N) >= 0 || s.Cmp(N) >= 0 {
		return false
	}

	// 调整算法细节以实现SM2
	t := new(big.Int).Add(r, s)    // t = r + s
	t.Mod(t, N)
	if t.Sign() == 0 {
		return false
	}

	var x *big.Int
	x1, y1 := c.ScalarBaseMult(s.Bytes())   // 计算s对应的公钥：（x1,y1） = s * G
	x2, y2 := c.ScalarMult(pub.X, pub.Y, t.Bytes()) //计算（x2,y2） = (r+s) * PUBKEY
	x, _ = c.Add(x1, y1, x2, y2)  //2个坐标相加后，取x轴：  s * (G + PUBKEY) + r * PUBKEY

	e := new(big.Int).SetBytes(hash)
	x.Add(x, e)    
	x.Mod(x, N)
	return x.Cmp(r)==0  // s * (G + PUBKEY) + r * PUBKEY + e  mod N == r
}

// hashToInt converts a hash value to an integer. There is some disagreement
// about how this is done. [NSA] suggests that this is done in the obvious
// manner, but [SECG] truncates the hash to the bit-length of the curve order
// first. We follow [SECG] because that's what OpenSSL does. Additionally,
// OpenSSL right shifts excess bits from the number if the hash is too large
// and we mirror that too.
// This is borrowed from crypto/ecdsa.
func hashToInt(hash []byte, c *Sm2P256Curve) *big.Int {
	orderBits := c.Params().N.BitLen()
	orderBytes := (orderBits + 7) / 8
	if len(hash) > orderBytes {
		hash = hash[:orderBytes]
	}

	ret := new(big.Int).SetBytes(hash)
	excess := len(hash)*8 - orderBits
	if excess > 0 {
		ret.Rsh(ret, uint(excess))
	}
	return ret
}
// decompressPoint decompresses a point on the given curve given the X point and
// the solution to use.
func decompressPoint(curve *Sm2P256Curve, x *big.Int, ybit bool) (*big.Int, error) {
	// TODO: This will probably only work for secp256k1 due to
	// optimizations.

	// Y = +-sqrt(x^3 + B)
	x3 := new(big.Int).Mul(x, x)
	x3.Mul(x3, x)
	x3.Add(x3, curve.Params().B)

	// Y = +-sqrt(x^3 + ax + B)
	var ax, x_ sm2P256FieldElement
	sm2P256FromBig(&x_, x)
	sm2P256Mul(&ax, &curve.a, &x_) // a = a * x
	x3.Add(x3, sm2P256ToBig(&ax))

	// now calculate sqrt mod p of x2 + B
	// This code used to do a full sqrt based on tonelli/shanks,
	// but this was replaced by the algorithms referenced in
	// https://bitcointalk.org/index.php?topic=162805.msg1712294#msg1712294
	y := new(big.Int).Exp(x3, curve.QPlus1Div4(), curve.Params().P)

	if ybit != isOdd(y) {
		y.Sub(curve.Params().P, y)
	}
	if ybit != isOdd(y) {
		return nil, fmt.Errorf("ybit doesn't match oddness")
	}
	return y, nil
}
// recoverKeyFromSignature This performs the details
// in the inner loop in Step 1. The counter provided is actually the j parameter
// of the loop * 2 - on the first iteration of j we do the R case, else the -R
// case in step 1.6. This counter is used in the bitcoin compressed signature
// format and thus we match bitcoind's behaviour here.
func recoverKeyFromSignature(curve *Sm2P256Curve, sig *Signature, msg []byte,iter int, doChecks bool) (*ecdsa.PublicKey, error) {
	
	e := hashToInt(msg, curve)
	
	Rx := new(big.Int).Mul(curve.Params().N, new(big.Int).SetInt64(int64(iter/2)))
	Rx.Add(Rx, sig.R)
	Rx.Sub(Rx, e)  // Rx = r -e 
	if Rx.Cmp(curve.Params().P) != -1 {
		return nil, errors.New("calculated Rx is larger than curve P")
	}
	Ry, err := decompressPoint(curve, Rx, iter%2 == 1)
	if err != nil {
		return nil, err
	}
	if doChecks {
		nRx, nRy := curve.ScalarMult(Rx, Ry, curve.Params().N.Bytes())
		if nRx.Sign() != 0 || nRy.Sign() != 0 {
			return nil, errors.New("n*R does not equal the point at infinity")
		}
	}
	
	t := new(big.Int).Add(sig.R, sig.S)    // t = r + s
	t.Mod(t, curve.Params().N)
	if t.Sign() == 0 {
		return nil, errors.New("t = r + s equal 0")
	}
	invr := new(big.Int).ModInverse(t, curve.Params().N)  // 1/t

	negS := new(big.Int).Neg(sig.S)
	negS.Mod(negS, curve.Params().N)

	x1, y1 := curve.ScalarBaseMult(negS.Bytes())   // 计算s对应的公钥：（x1,y1） = -s * G
	Qx, Qy := curve.Add(Rx, Ry, x1, y1)    //  (Rx,Ry) - s*G
	sRx, sRy := curve.ScalarMult(Qx, Qy, invr.Bytes())  // pub = ((Rx,Ry) - s*G)  / (r+s)

	return &ecdsa.PublicKey{
		Curve: curve,
		X:     sRx,
		Y:     sRy,
	}, nil
}
// 参考比特币代码恢复公钥
func recoverCompact(curve *Sm2P256Curve, signature, hash []byte) (*ecdsa.PublicKey, bool, error) {
	bitlen := (curve.BitSize + 7) / 8
	if len(signature) != 1+bitlen*2 {
		return nil, false, errors.New("invalid compact signature size")
	}

	iteration := int((signature[0] - 27) & ^byte(4))

	// format is <header byte><bitlen R><bitlen S>
	sig := &Signature{
		R: new(big.Int).SetBytes(signature[1 : bitlen+1]),
		S: new(big.Int).SetBytes(signature[bitlen+1:]),
	}
	// The iteration used here was encoded
	key, err := recoverKeyFromSignature(curve, sig, hash, iteration, false)
	if err != nil {
		return nil, false, err
	}

	return key, ((signature[0] - 27) & 4) == 4, nil
}
// Ecrecover returns the uncompressed public key that created the given signature.
func Ecrecover(hash, sig []byte) ([]byte, error) {
	pub, err := SigToPub(hash, sig)
	if err != nil {
		return nil, err
	}
	b := make([]byte, 0, PubKeyBytesLenUncompressed)
	b = append(b, pubkeyUncompressed)
	b = paddedAppend(32, b, pub.X.Bytes())
	return paddedAppend(32, b, pub.Y.Bytes()), nil
}

// SigToPub returns the public key that created the given signature.
func SigToPub(hash, sig []byte) (*ecdsa.PublicKey, error) {
	if len(sig) != 65 {
		return nil, errors.New("invalid signiture length")
	}
	// Convert to btcec input format with 'recovery id' v at the beginning.
	btcsig := make([]byte, 65)
	btcsig[0] = sig[64] + 27
	copy(btcsig[1:], sig)

	pub, _, err := recoverCompact(P256Sm2(), btcsig, hash)
	return (*ecdsa.PublicKey)(pub), err
}
// DecompressPubkey parses a public key in the 33-byte compressed format.
func DecompressPubkey(pubkey []byte) (*ecdsa.PublicKey, error) {
	if len(pubkey) != 33 {
		return nil, errors.New("invalid compressed public key length")
	}
	var aa, xx, xx3 sm2P256FieldElement

	S256()
	prefix := byte(pubkey[0])  
	ybit := (prefix & 0x1) == 0x1  //前缀=2，y是偶数，ybit=false；前缀=3，y是奇数，ybit=true
	prefix &= ^byte(0x1)  //将最低位清0，即设置prefix=2
	if prefix != pubkeyCompressed {
		return nil, fmt.Errorf("invalid magic in compressed pubkey string: %d", prefix)
	}

	x := new(big.Int).SetBytes(pubkey[1:])  //取出x坐标轴
	curve := sm2P256

	// 根据公式计算y： y^2 = x^3 + a*x + b
	sm2P256FromBig(&xx, x)
	sm2P256Square(&xx3, &xx)       // x3 = x ^ 2
	sm2P256Mul(&xx3, &xx3, &xx)    // x3 = x ^ 2 * x
	sm2P256Mul(&aa, &curve.a, &xx) // a = a * x
	sm2P256Add(&xx3, &xx3, &aa)
	sm2P256Add(&xx3, &xx3, &curve.b)

	y2 := sm2P256ToBig(&xx3)
	y := new(big.Int).ModSqrt(y2, sm2P256.P)

	if isOdd(y) != ybit { //如果y的奇偶性不一致， 需要进行转换
		y.Sub(sm2P256.P, y)
	}

	if ybit != isOdd(y) {
		return nil, fmt.Errorf("ybit doesn't match oddness")
	}
	if x.Cmp(P256Sm2().Params().P) >= 0 {
		return nil, fmt.Errorf("pubkey X parameter is >= to P")
	}
	if y.Cmp(P256Sm2().Params().P) >= 0 {
		return nil, fmt.Errorf("pubkey Y parameter is >= to P")
	}
	if !P256Sm2().IsOnCurve(x, y) {
		return nil, fmt.Errorf("pubkey isn't on secp256k1 curve")
	}
	return &ecdsa.PublicKey{
		Curve: P256Sm2(),
		X:     x,
		Y:     y,
	}, nil
}

// CompressPubkey encodes a public key to the 33-byte compressed format.
func CompressPubkey(pubkey *ecdsa.PublicKey) []byte {
	buf := []byte{}
	buf = append(buf, pubkey.X.Bytes()...)  //提取x轴坐标
	if n := len(pubkey.X.Bytes()); n < 32 {  //如果x坐标轴不足32字节，在前面补0.
		buf = append(zeroByteSlice()[:(32-n)], buf...)
	}
	prefix := pubkeyCompressed
	if isOdd(pubkey.Y) {    // 奇数：0x3； 偶数：0x2 
		prefix |= 0x1
	}
	buf = append([]byte{prefix}, buf...) //压缩公钥格式为：1字节y轴奇偶标志位 || 32字节x轴
	return buf
}

// S256 returns an instance of the secp256k1 curve.
func S256() elliptic.Curve {
	return P256Sm2()
}

// func UnmarshalPubkey(pub []byte) (*ecdsa.PublicKey, error) {
// 	x, y := elliptic.Unmarshal(S256(), pub)
// 	if x == nil {
// 		return nil, errInvalidPubkey
// 	}
// 	return &ecdsa.PublicKey{Curve: S256(), X: x, Y: y}, nil
// }

// func FromECDSAPub(pub *ecdsa.PublicKey) []byte {
// 	if pub == nil || pub.X == nil || pub.Y == nil {
// 		return nil
// 	}
// 	return elliptic.Marshal(S256(), pub.X, pub.Y)
// }
// func GenerateKey() (*ecdsa.PrivateKey, error) {
// 	return ecdsa.GenerateKey(S256(), rand.Reader)
// }

// toECDSA creates a private key with the given D value. The strict parameter
// controls whether the key's length should be enforced at the curve size or
// it can also accept legacy encodings (0 prefixes).
// func toECDSA(d []byte, strict bool) (*ecdsa.PrivateKey, error) {
// 	priv := new(ecdsa.PrivateKey)
// 	priv.PublicKey.Curve = S256()
// 	if strict && 8*len(d) != priv.Params().BitSize {
// 		return nil, fmt.Errorf("invalid length, need %d bits", priv.Params().BitSize)
// 	}
// 	priv.D = new(big.Int).SetBytes(d)

// 	// The priv.D must < N
// 	if priv.D.Cmp(secp256k1N) >= 0 {
// 		return nil, fmt.Errorf("invalid private key, >=N")
// 	}
// 	// The priv.D must not be zero or negative.
// 	if priv.D.Sign() <= 0 {
// 		return nil, fmt.Errorf("invalid private key, zero or negative")
// 	}

// 	priv.PublicKey.X, priv.PublicKey.Y = priv.PublicKey.Curve.ScalarBaseMult(d)
// 	if priv.PublicKey.X == nil {
// 		return nil, errors.New("invalid private key")
// 	}
// 	return priv, nil
// }