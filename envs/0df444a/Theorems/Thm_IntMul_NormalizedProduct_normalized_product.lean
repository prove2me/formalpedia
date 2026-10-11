-- Prove2me | Theorems.Thm_IntMul_NormalizedProduct_normalized_product
-- name    : IntMul.NormalizedProduct.normalized_product
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T14:03:22.790742+00:00
-- url     : https://prove2.me/theorems/583618fe-9d2d-410f-9d99-2a60e7b1714e
-- title:
--   Complete physical product normalization with descriptor preparation and exact operand-sum output width
-- statement:
--   Let $x,y,z,l,d$ be finite binary words. Write $B=\operatorname{val}(z)+1$, $m_x,m_y$ for the retained base-$2^B$ operand block counts, $N=2B+\lceil\log_2\min(m_x,m_y)\rceil$ using the natural-number ceiling-log convention at zero, and $W=\operatorname{val}(d)+1$. Suppose $\operatorname{val}(l)+1=N$ and $W=|x|+|y|$. From the explicit physical caller frame containing the padded convolution coefficients, zero saved carry, retained arithmetic descriptors and desired-width word $d$, a fixed sixteen-tape machine halts in its exact terminal configuration within
--
--   $$(m_x+m_y)(41N+32B+21|z|+4|l|+126)+10W+6|d|+63$$
--
--   actual transitions. Its output is exactly the big-endian $W$-bit representation of $\operatorname{val}(x)\operatorname{val}(y)$, including its leading-zero padding. All carry arithmetic, output ordering, descriptor preparation, width conversion, scratch erasures and three outer caller returns are charged. The original prepared coefficient bank, canonical zero saved carry, retained descriptors and the entire specified work-bank frame are retained or restored as stated by the exact terminal configuration. For equally long operands this returns the required $2n$-bit output. Coefficient generation, loading and global initialization remain explicit caller obligations.
-- source:
--   Original complete literal physical product normalization pipeline. Owns all three native embeddings, complete handoffs, physical return-frame equality, padding bounds, product value preservation and complete clock. Written by Codex.

import Definitions.Def_IntMul_NormalizedProduct
import Mathlib.Tactic
import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits

open IntMul IntMul.NormalizedProduct

theorem IntMul.NormalizedProduct.normalized_product (base : machine.Cfg) (pre x y z l d : List Bool)
    (hl : val l+1=CarryProduct.coefficientWidth (CarryStep.blockSize z) x y)
    (hd : FixedOutputWidth.width d=x.length+y.length) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*CarryProduct.coefficientWidth (CarryStep.blockSize z) x y+32*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+10*FixedOutputWidth.width d+6*d.length+63 ∧
      machine.step^[t] (initialFrame base pre x y z l d)=finalFrame base pre x y z l d ∧
      (machine.step^[t] (initialFrame base pre x y z l d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base pre x y z l d)).cells 1=
        machine.tapeOf ((bin (x.length+y.length) (val x*val y)).map machine.bitSym) := by sorry
