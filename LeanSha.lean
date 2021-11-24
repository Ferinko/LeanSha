namespace Sha

def BitsInByte : UInt64 := 8

def h₀α : UInt32 := 0x67452301
def h₁α : UInt32 := 0xEFCDAB89
def h₂α : UInt32 := 0x98BADCFE
def h₃α : UInt32 := 0x10325476
def h₄α : UInt32 := 0xC3D2E1F0

def BlockSize : UInt32 := 512
def OctetsInBlock : UInt32 := BlockSize / 8

def OctetsInUInt64 : Nat := 8

structure Msg where data : ByteArray deriving Inhabited

structure Block where data : ByteArray deriving Inhabited

def prepare (msg : ByteArray) : Msg := do
  assert! msg.size ≤ 2^64 / BitsInByte.toNat
  let mut msg' := msg
  msg' := msg'.push 0b10000000
  msg' := padToBlockSizeMinusOne msg'
  msg' := msg'.append lengthBigEndian
  ⟨msg'⟩
  where
    padToBlockSizeMinusOne (arr : ByteArray) : ByteArray :=
      ByteArray.append arr ⟨⟨
        List.replicate ((OctetsInBlock.toNat - (msg.size + OctetsInUInt64 + 1) % OctetsInBlock.toNat) % (OctetsInBlock.toNat)) 0x00
      ⟩⟩
    lengthBigEndian : ByteArray :=
      let sz : UInt64 := UInt64.ofNat msg.size * BitsInByte
      ⟨#[
        (sz >>> (7 * BitsInByte)),
        (sz >>> (6 * BitsInByte)),
        (sz >>> (5 * BitsInByte)),
        (sz >>> (4 * BitsInByte)),
        (sz >>> (3 * BitsInByte)),
        (sz >>> (2 * BitsInByte)),
        (sz >>> (1 * BitsInByte)),
        (sz >>> (0 * BitsInByte))
      ].map (·.toUInt8)⟩

def blocks (msg : Msg) : Array Block :=
  (·.1) <| msg.data.data.foldl (init := (#[], ByteArray.empty, 0))
    λ (res, stride, depth) octet =>
      if depth % OctetsInBlock = OctetsInBlock - 1
      then (res.push ⟨stride.push octet⟩, ⟨#[]⟩, depth + 1)
      else (res, stride.push octet, depth + 1)

def OctetsInUInt32 : Nat := 4

def UInt32sOfBlock (block : Block) : Array UInt32 := do
  let blockData : Array UInt8 := block.data.data
  let mut ui32 : UInt32 := 0
  let mut res : Array UInt32 := #[]
  for byte in [: block.data.size : OctetsInUInt32] do
    ui32 := (blockData.get! (byte + 0)).toUInt32 <<< (3 * BitsInByte).toUInt32 |||
            (blockData.get! (byte + 1)).toUInt32 <<< (2 * BitsInByte).toUInt32 |||
            (blockData.get! (byte + 2)).toUInt32 <<< (1 * BitsInByte).toUInt32 |||
            (blockData.get! (byte + 3)).toUInt32 <<< (0 * BitsInByte).toUInt32
    res := res.push ui32
  res

def ByteArrayOfUInt32 (ui32 : UInt32) : ByteArray :=
  ⟨#[
    ui32 >>> (BitsInByte.toUInt32 * 3),
    ui32 >>> (BitsInByte.toUInt32 * 2),
    ui32 >>> (BitsInByte.toUInt32 * 1),
    ui32 >>> (BitsInByte.toUInt32 * 0)
  ].map (·.toUInt8)⟩

structure ShaST where
  h₀ : UInt32
  h₁ : UInt32
  h₂ : UInt32
  h₃ : UInt32
  h₄ : UInt32

def ShaST.mkInit : ShaST := {
  h₀ := h₀α
  h₁ := h₁α
  h₂ := h₂α
  h₃ := h₃α
  h₄ := h₄α
}

def NumIntegerPadBegin : Nat := 16
def NumIntegerPadEnd : Nat := 79

def rotl (n : UInt32) (k : Nat := 1) : UInt32 :=
  assert! k ≤ 32
  n <<< k.toUInt32 ||| (n >>> (32 - k.toUInt32))

def bneg (n : UInt32) : UInt32 := n.xor 0xFFFFFFFF

def sha1 (msg : ByteArray) : ByteArray :=
  let msgBlocks : Array Block := blocks ∘ prepare <| msg
  do
    let mut st : ShaST := ShaST.mkInit
    for block in msgBlocks do
      let mut uInts : Array UInt32 := UInt32sOfBlock block
      for i in [NumIntegerPadBegin : NumIntegerPadEnd + 1] do
        uInts := uInts.push <| rotl (
          uInts[i - 3] ^^^ uInts[i - 8] ^^^
          uInts[i - 14] ^^^ uInts[i - 16]
        )
      let mut a : UInt32 := st.h₀
      let mut b : UInt32 := st.h₁
      let mut c : UInt32 := st.h₂
      let mut d : UInt32 := st.h₃
      let mut e : UInt32 := st.h₄
      let mut f : UInt32 := 0
      let mut k : UInt32 := 0
      for i in [0 : NumIntegerPadEnd + 1] do
        if 0 ≤ i ∧ i ≤ 19 then 
          f := (b &&& c) ||| ((bneg b) &&& d)
          k := 0x5A827999
        else if 20 ≤ i ∧ i ≤ 39 then
          f := b ^^^ c ^^^ d
          k := 0x6ED9EBA1
        else if 40 ≤ i ∧ i ≤ 59 then 
          f := (b &&& c) ||| (b &&& d) ||| (c &&& d) 
          k := 0x8F1BBCDC
        else 
          f := b ^^^ c ^^^ d
          k := 0xCA62C1D6
        let temp := (rotl a 5) + f + e + k + uInts[i]
        e := d
        d := c
        c := rotl b 30
        b := a
        a := temp
      st := ⟨st.h₀ + a, st.h₁ + b, st.h₂ + c, st.h₃ + d, st.h₄ + e⟩
    pure ⟨
      ByteArrayOfUInt32 st.h₀ ++ ByteArrayOfUInt32 st.h₁ ++ 
      ByteArrayOfUInt32 st.h₂ ++ ByteArrayOfUInt32 st.h₃ ++ 
      ByteArrayOfUInt32 st.h₄ |>.data
    ⟩

end Sha