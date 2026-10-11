-- Prove2me | Theorems.Thm_IntMul_CarryProduct_carry_product
-- name    : IntMul.CarryProduct.carry_product
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T13:10:25.91268+00:00
-- url     : https://prove2.me/theorems/74069f52-a9b9-485c-a12c-647a7002d0e0
-- title:
--   Actual physical product recovery from a prepared convolution coefficient frame
-- statement:
--   Let $x,y$ be finite binary operand words. Write $B=\operatorname{val}(z)+1$, let $m_x,m_y$ be their retained base-$2^B$ block counts, and let $N=2B+\lceil\log_2\min(m_x,m_y)\rceil$ with the natural-number ceiling-log convention at zero. Suppose the supplied width descriptor satisfies $\operatorname{val}(l)+1=N$. From the explicit prepared caller frame containing the product convolution coefficients padded to width $N$, a zero carry of width $N$, and the retained descriptors, a fixed fifteen-tape machine halts in its exact terminal configuration after at most
--
--   $$(m_x+m_y)\bigl(41N+21B+21|z|+4|l|+126\bigr)+21$$
--
--   physical transitions. Its output is exactly the big-endian binary representation of $\operatorname{val}(x)\operatorname{val}(y)$ padded to $B(m_x+m_y)$ bits, and its saved carry tape contains the canonical $N$-bit zero word. All arithmetic, carry traversal, temporary-bank erasures, output reversal and finite-caller returns are included. This realizes the complete physical product-recovery stage; the incoming coefficient generation and loading costs remain separate caller obligations.
-- source:
--   Original complete physical product recovery from prepared coefficients. Owns exact coefficient encoding, width verification, actual output-tape product identification and canonical zero saved-carry proof. Uses accepted carry/output and convolution/carry recovery interfaces. Written by Codex.

import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic
import Definitions.Def_IntMul_CarryProduct

open IntMul IntMul.CarryProduct

theorem IntMul.CarryProduct.carry_product (pre x y z l : List Bool)
    (hl : val l+1=coefficientWidth (CarryStep.blockSize z) x y) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*coefficientWidth (CarryStep.blockSize z) x y+21*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+21 ∧
      machine.step^[t] (initialFrame pre x y z l)=finalFrame pre x y z l ∧
      (machine.step^[t] (initialFrame pre x y z l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 1=
        machine.tapeOf ((bin (CarryStep.blockSize z*
          (DigitConvolution.blockCount (CarryStep.blockSize z) x+
            DigitConvolution.blockCount (CarryStep.blockSize z) y)) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 12=
        machine.tapeOf ((bin (coefficientWidth (CarryStep.blockSize z) x y) 0).map machine.bitSym) := by sorry
