package main

import (
	"fmt"
	"runtime"
	"time"
	"strings"
	"strconv"
	"os"
	"math/big"
	"crypto/rand"
	"encoding/hex"

	"golang.org/x/crypto/sha3"
	"github.com/deroproject/derohe/transaction"
	"github.com/deroproject/derohe/rpc"
	"github.com/deroproject/derohe/walletapi/mnemonics"
	"github.com/deroproject/derohe/cryptography/crypto"
	"github.com/deroholic/derogo"
)

const N = 32*1024
var threads = runtime.GOMAXPROCS(0)
var language string
var output *os.File
var daemon_address = "127.0.0.1:10102"

type result_t struct {
	txn *transaction.Transaction
	secret *big.Int
}

type pt_t struct {
	x, y, secret *big.Int
}

func mySetBig(s string) (*big.Int) {
	i, _ := new(big.Int).SetString(s, 0)
	return i
}

// Dero's G1
var GXMONT = mySetBig("0x26b1948aba4465c168faeb79586c8022afdf98edf532bd9d62ce90cd019391e5")
var GYMONT = mySetBig("0x24c3da4404b3a717f30e6db01e4ef1d4cea805087c00ad93893ab6f1e1aa1f4e")
var G = &pt_t{GXMONT, GYMONT, ZERO}
// Dero's field
var P = mySetBig("21888242871839275222246405745257275088696311157297823662689037894645226208583")
var NP = mySetBig("0xf57a22b791888c6bd8afcbd01833da809ede7d651eca6ac987d20782e4866389")
var R2 = mySetBig("0x06d89f71cab8351f47ab1eff0a417ff6b5e71911d44501fbf32cfc5b538afa89")
var O = mySetBig("21888242871839275222246405745257275088548364400416034343698204186575808495617")
var NO = mySetBig("0x73f82f1d0d8341b2e39a9828990623916586864b4c6911b3c2e1f593efffffff")
var OR = mySetBig("0x54a47462623a04a7ab074a58680730147144852009e880ae620703a6be1de925")
var OR2 = mySetBig("0x216d0b17f4e44a58c49833d53bb808553fe3ab1e35c59e31bb8e645ae216da7")

var ONE = mySetBig("1")
var ZERO = mySetBig("0")
var inc = &pt_t{GXMONT, GYMONT, ONE}

func randPt(bits int64) (*pt_t) {
        rnd := big.NewInt(0).Exp(big.NewInt(2), big.NewInt(bits), nil)
        rnd, _ = rand.Int(rand.Reader, rnd)

        p := newPt()
        curveMul(p, G, rnd)
        p.secret.Set(rnd)

        return p
}

func newPt() (*pt_t) {
	p := pt_t{new(big.Int).Set(ZERO), new(big.Int).Set(ZERO), new(big.Int).Set(ZERO)}

	return &p
}

func (a *pt_t) set(b *pt_t) {
	a.x = b.x
	a.y = b.y
}

func (a *pt_t) setInfinity() {
	a.x.Set(ZERO)
	a.y.Set(ZERO)
}

func (p *pt_t) String() (string) {
	return fmt.Sprintf("bn256.G1(%064x, %064x)", p.x, p.y)
}

// https://www.nayuki.io/page/barrett-reduction-algorithm
func barretReductionO(a *big.Int) {
	t := new(big.Int).Mul(a, OR)
	t.Rsh(t, 508)
	t.Mul(t, O)
	a.Sub(a, t)

	if a.Cmp(O) > 0 {a.Sub(a, O)}
}

func modMulP(p, a, b *big.Int) {
	modMul(p, a, b, P, NP)
}

func modMulO(p, a, b *big.Int) {
	modMul(p, a, b, O, NO)
}

func modMul(p, a, b, M, NM *big.Int) {
	var T = new(big.Int)
	var m = new(big.Int)
	var t = new(big.Int)
	var abs []big.Word

	if a.Cmp(ZERO) == 0 || b.Cmp(ZERO) == 0 {
		p.Set(ZERO)
		return
	}

	T.Mul(a, b)
	abs = T.Bits()

	m.Mul(new(big.Int).SetBits(abs[0:4]), NM)
	abs = m.Bits()

	t.Mul(new(big.Int).SetBits(abs[0:4]), M)

	p.Add(T, t)

	abs = p.Bits()
	p.SetBits(abs[4:8])
	if p.Cmp(M) > 0 { p.Sub(p, M) }	// don't know why this is needed sometimes
}

// https://crypto.stackexchange.com/a/54623/555
func myInvert(a, p *big.Int) (r *big.Int) {
	u := new(big.Int).Set(a)
	v := new(big.Int).Set(p)
	x2 := new(big.Int).Set(ZERO)
	x1 := new(big.Int).Set(p); x1.Sub(x1, ONE)

	if u.Bit(0) == 0 {
		u.Add(a, p)
	}

	for v.Cmp(ONE) != 0 {
		for v.Cmp(u) < 0 {
			u.Sub(u, v)
			x1.Add(x1, x2)

			for u.Bit(0) == 0 {
				if x1.Bit(0) == 1 {
					x1.Add(x1, p)
				}
				u.Rsh(u, 1)
				x1.Rsh(x1, 1)
			}
		}

		v.Sub(v, u)
		x2.Add(x2, x1)

		for v.Bit(0) == 0 {
			if x2.Bit(0) == 1 {
				x2.Add(x2, p)
			}
			v.Rsh(v, 1)
			x2.Rsh(x2, 1)
		}
	}

	r = x2

	return
}

func montEncode(r, a *big.Int) {
	modMulP(r, a, R2)
}

func montDecode(r, a *big.Int) {
	modMulP(r, a, ONE)
}

func curveAddG(c, a *pt_t) {
	curveAdd(c, a, G)
}

// https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication
func curveDouble(c, a *pt_t) {
	var t1 = new(big.Int)
	var t2 = new(big.Int)
	var inv = new(big.Int)
	var s = new(big.Int)
	var s2 = new(big.Int)
	var rx = new(big.Int)
	var ry = new(big.Int)

	modMulP(t1, a.y, big.NewInt(2))
	modMulP(t2, a.x, a.x)
	modMulP(t2, t2, big.NewInt(3))

	montDecode(inv, t1)
	inv.ModInverse(inv, P)
	montEncode(inv, inv)

	modMulP(s, t2, inv)
	modMulP(s2, s, s)

	rx.Sub(s2, a.x)
	if rx.Sign() < 0 { rx.Add(rx, P) }

	rx.Sub(rx, a.x)
	if rx.Sign() < 0 { rx.Add(rx, P) }

	ry.Sub(a.x, rx)
	if ry.Sign() < 0 { ry.Add(ry, P) }

	modMulP(ry, ry, s)

	ry.Sub(ry, a.y)
	if ry.Sign() < 0 { ry.Add(ry, P) }

	c.x = rx
	c.y = ry
}

func curveAdd(c, a, b *pt_t) {
	if a.x.Cmp(ZERO) == 0 && a.y.Cmp(ZERO) == 0 {
		c.x = b.x
		c.y = b.y
		return
	}
	if b.x.Cmp(ZERO) == 0 && b.y.Cmp(ZERO) == 0 {
		c.x = a.x
		c.y = a.y
		return
	}

	if a.x == b.x && a.y == b.y {
		curveDouble(c, a)
		return
	}

	var t1 = new(big.Int)
	var t2 = new(big.Int)
	var inv = new(big.Int)
	var s = new(big.Int)
	var s2 = new(big.Int)
	var rx = new(big.Int)
	var ry = new(big.Int)

	t1.Sub(b.x, a.x)
	if t1.Sign() < 0 { t1.Add(t1, P) }

	t2.Sub(b.y, a.y)
	if t2.Sign() < 0 { t2.Add(t2, P) }

	montDecode(inv, t1)
//	inv = myInvert(inv, P)
	inv.ModInverse(inv, P)
	montEncode(inv, inv)

	modMulP(s, t2, inv)
	modMulP(s2, s, s)

	rx.Sub(s2, a.x)
	if rx.Sign() < 0 { rx.Add(rx, P) }

	rx.Sub(rx, b.x)
	if rx.Sign() < 0 { rx.Add(rx, P) }

	ry.Sub(a.x, rx)
	if ry.Sign() < 0 { ry.Add(ry, P) }

	modMulP(ry, ry, s)

	ry.Sub(ry, a.y)
	for ry.Sign() < 0 { ry.Add(ry, P) }

	c.x = rx
	c.y = ry
}

func curveMul(r, a *pt_t, s *big.Int) {
	res := newPt()
	tmp := newPt()
	tmp.set(a)

	for i:= 0; i < s.BitLen(); i++ {
		if s.Bit(i) == 1 {
			curveAdd(res, res, tmp)
		}
		curveDouble(tmp, tmp)
	}

	r.set(res)
}

func pointFactory(p *pt_t) (* pt_t){
	curveAdd(p, p, inc)
	p.secret.Add(p.secret, inc.secret)

	return p
}

func listInit(ctx *pt_t) ([]*pt_t) {
	pList := make([]*pt_t, N)

	// initial point
	p := pointFactory(ctx)

	// make point list
	for i := 0; i < N; i++ {
		pList[i] = newPt()
		montDecode(pList[i].x, p.x)
		montDecode(pList[i].y, p.y)
		pList[i].secret.Set(p.secret)

		p = pointFactory(ctx)
	}

	return pList
}

func listNext(pList []*pt_t) {
	var scratch = make([]big.Int, N)
	var accum = new(big.Int).Set(ONE)
	var accum_inv = new(big.Int)
	var inv = new(big.Int)
	var t1 = new(big.Int)
	var t2 = new(big.Int)
	var rx = new(big.Int)
	var ry = new(big.Int)
	var s = new(big.Int)
	var s2 = new(big.Int)

	for i := 0; i < N; i++ {
		t1.Sub(G.x, pList[i].x)
		if t1.Sign() < 0 { t1.Add(t1, P) }

		scratch[i].Set(accum)
		modMulP(accum, accum, t1)
	}

	montDecode(accum, accum)
	accum.ModInverse(accum, P)
//	accum = myInvert(accum, P)
	montEncode(accum_inv, accum)

	for i := N-1; i >= 0; i-- {
		t1.Sub(G.x, pList[i].x)
		if t1.Sign() < 0 { t1.Add(t1, P) }

		modMulP(inv, accum_inv, &scratch[i])
		modMulP(accum_inv, accum_inv, t1)

		t2.Sub(G.y, pList[i].y)
		if t2.Sign() < 0 { t2.Add(t2, P) }

		modMulP(s, t2, inv)
		modMulP(s2, s, s)

		rx.Sub(s2, pList[i].x)
		if rx.Sign() < 0 { rx.Add(rx, P) }

		rx.Sub(rx, G.x)
		if rx.Sign() < 0 { rx.Add(rx, P) }

		ry.Sub(pList[i].x, rx)
		if ry.Sign() < 0 { ry.Add(ry, P) }

		modMulP(ry, ry, s)

		ry.Sub(ry, pList[i].y)
		for ry.Sign() < 0 { ry.Add(ry, P) }

/* validation
var c = newPt()
ns := new(big.Int).Add(pList[i].secret, ONE)
curveMul(c, G, ns)
//curveAdd(c, G, pList[i])
if rx.Cmp(c.x) != 0 {
	fmt.Printf("X = %064x\n", pList[i].x)
	fmt.Printf("Y = %064x\n", pList[i].y)
	fmt.Printf("cx = %064x\n", c.x)
	fmt.Printf("rx = %064x\n", rx)
	fmt.Printf("cy = %064x\n", c.y)
	fmt.Printf("ry = %064x\n", ry)
	fmt.Printf("ERROR [%d]\n", i)
}
*/
		pList[i].x.Set(rx)
		pList[i].y.Set(ry)
		pList[i].secret.Add(pList[i].secret, ONE)
	}
}

func parseOpt(param string) {
        s := strings.Split(param, "=")

        if len(s) > 1 && s[0] == "--daemon-address" {
                daemon_address = s[1]
        } else if len(s) > 1 && s[0] == "--output" {
		var err error
		output, err = os.OpenFile(s[1], os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
		if err != nil {
			fmt.Printf("Cannot open file '%s' for writing\n", s[1])
			os.Exit(0)
		}
		fmt.Printf("Output to file '%s'\n", s[1])
        } else if len(s) > 1 && s[0] == "--language" {
		language = s[1]
        } else if len(s) > 1 && s[0] == "--threads" {
		threads, _ = strconv.Atoi(s[1])
		if threads < 1 {
			fmt.Printf("threads must > 0\n")
			os.Exit(0)
		}
        } else if s[0] == "--help" {
                fmt.Printf("fastreg [--help] [--daemon-address=<127.0.0.1:10102>] [--threads=<8>] [--language=<English>] [--output=<filename>]\n")
                os.Exit(0)
        } else {
                fmt.Printf("invalid argument '%s', skipping\n", param)
        }
}

func getOpts() {
        for i:= 0; i < len(os.Args[1:]); i++ {
                param := os.Args[i+1]
                if param[0] == '-' && param[1] == '-' {
                        parseOpt(param)
                } else {
                }
        }
}

func main() {
	getOpts()
	defer output.Close()

	if output == nil {
		derogo.DeroInit(daemon_address)
	}

	inc = randPt(192)

	fmt.Printf("starting %d thread(s)\n", threads)

	results := make(chan result_t)

	for i := 0; i < threads; i++ {
		go search(i, results)
	}

	now := time.Now()
	for true {
		result := <-results
		if !result.txn.IsRegistrationValid() {
			panic("registration tx could not be generated. something failed.")
		}

		a, _ := rpc.NewAddressFromCompressedKeys(result.txn.MinerAddress[:])
		fmt.Printf("%s\n", a.String())
		fmt.Printf("%s\n", mnemonics.Key_To_Words(result.secret, language))
		fmt.Printf("%064x\n", result.secret)

		tran := result.txn.Serialize()

		if output == nil {
			err := derogo.DeroSendRegTxn(tran)
			if err != nil {
				fmt.Printf("Error submitting registration tx: %s\n", err)
			} else {
				fmt.Printf("Transaction submitted: txid = %s\n", result.txn.GetHash())
			}
		} else {
			fmt.Fprintf(output, "%064x %s\n", result.secret, hex.EncodeToString(tran))
		}

		break
	}
	fmt.Printf("Elapsed time: %s\n", time.Since(now))
}

func search(threadId int, c chan result_t) {
	ctx := randPt(255)
	pList := listInit(ctx)

	tmpPoint := randPt(255)

	j := 0
	for true {
		tp := newPt()
		montDecode(tp.x, tmpPoint.x)
		montDecode(tp.y, tmpPoint.y)
		tp.secret.Set(tmpPoint.secret)

		for i := 0; i < N; i++ {
			txn := getRegistrationTX(pList[i], tp)

			hash := GetHash(txn)
			if hash[0] == 0 && hash[1] == 0 && hash[2] == 0 {
				result := result_t{txn, pList[i].secret}
				c <- result
//				fmt.Printf("[%02d] %d, %064x %064x txid=%x\n", threadId, j, pList[i].secret, tp.secret, hash)

				// replacement point
				pList[i] = pointFactory(ctx)
			}
			j++
		}

		tmpPoint = pointFactory(tmpPoint)
	}
}

func getRegistrationTX(p, tp *pt_t) *transaction.Transaction {
	var tx transaction.Transaction
	tx.Version = 1
	tx.TransactionType = transaction.REGISTRATION

	addr := compress(p)
	copy(tx.MinerAddress[:], addr[:])

	c, s := sign(p, tp)
	c.FillBytes(tx.C[:])
	s.FillBytes(tx.S[:])

/*
	if !tx.IsRegistrationValid() {
		panic("registration tx could not be generated. something failed.")
	} else {
		fmt.Println("Reg OK")
	}
*/

	return &tx
}

func sign(p, tp *pt_t) (c, s *big.Int) {
	serialize := []byte(p.String() + tp.String()) // 280 bytes
	c = HashtoNumber(serialize)
	barretReductionO(c)

	s = new(big.Int).Mul(c, p.secret)
	barretReductionO(s)

//	s = new(big.Int)
//	modMulO(s, c, OR2)
//	modMulO(s, s, p.secret)

	s = s.Add(s, tp.secret)
	barretReductionO(s)

	return
}

func compress(p *pt_t) ([]byte) {
	b := make([]byte, 32)
	p.x.FillBytes(b)
	b = append(b, 0x00)

	// p.y >= P/2 ?
	y2 := new(big.Int).Rsh(P, 1)
	if p.y.Cmp(y2) >= 0 {
		b[32] = 0x01
	}


	return b
}

func HashtoNumber(input []byte) *big.Int {
        hasher := sha3.NewLegacyKeccak256()
        hasher.Write(input)

        hash := hasher.Sum(nil)
        return new(big.Int).SetBytes(hash[:])
}

const HashLength = 32
type Hash [HashLength]byte

func GetHash(tx *transaction.Transaction) (result Hash) {
	switch tx.Version {
	case 1:
		result = Hash(crypto.Keccak256(tx.SerializeCoreStatement())) // 101 bytes
	default:
		panic("Transaction version unknown")

	}
	return
}
