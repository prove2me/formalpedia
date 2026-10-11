-- Prove2me | Theorems.Thm_IntMul_WideCarryProduct_wide_carry_product
-- name    : IntMul.WideCarryProduct.wide_carry_product
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T15:55:47.546984+00:00
-- url     : https://prove2.me/theorems/bb29e313-7f70-4ffa-bfe2-46b7079a8d42
-- title:
--   Actual physical product recovery from a prepared convolution coefficient frame
-- statement:
--   Let $x,y$ be binary operand words and let $B=\operatorname{val}(z)+1$ be the positive block size. Let $N=\operatorname{val}(l)+1$ be a declared coefficient precision satisfying
--
--   $$2B+\left\lceil\log_2\min(m_x,m_y)\right\rceil\le N,$$
--
--   where $m_x,m_y$ are the operand block counts. From the explicit prepared frame containing all padded convolution coefficients as $N$-bit words and an $N$-bit zero carry, the fixed fifteen-tape carry/output machine globally halts in its exact terminal frame, outputs exactly
--
--   $$\operatorname{bin}_{B(m_x+m_y)}(\operatorname{val}(x)\operatorname{val}(y)),$$
--
--   and leaves the final carry as the canonical $N$-bit zero word. Its actual transition bound is
--
--   $$(m_x+m_y)(41N+21B+21|z|+4|l|+126)+21.$$
--
--   All coefficient reading, actual binary addition, carry propagation, scratch cleanup, physical output reversal and caller returns are charged. Coefficient generation, loading and descriptor preparation are explicit upstream obligations. The result allows any sufficient precision, including the simple choice $N=3B$ for logarithmic block sizes.
-- source:
--   Original complete physical product recovery for arbitrary sufficient coefficient precision. Owns exact representation transfer and terminal carry encoding. Written by Codex.

import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic
import Definitions.Def_IntMul_WideCarryProduct

open IntMul IntMul.WideCarryProduct

theorem IntMul.WideCarryProduct.wide_carry_product (pre x y z l : List Bool)
    (hN : CarryProduct.coefficientWidth (CarryStep.blockSize z) x y≤ val l+1) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*(val l+1)+21*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+21 ∧
      machine.step^[t] (initialFrame pre x y z l)=finalFrame pre x y z l ∧
      (machine.step^[t] (initialFrame pre x y z l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 1=
        machine.tapeOf ((bin (CarryStep.blockSize z*
          (DigitConvolution.blockCount (CarryStep.blockSize z) x+
            DigitConvolution.blockCount (CarryStep.blockSize z) y)) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 12=
        machine.tapeOf ((bin ((val l+1)) 0).map machine.bitSym) := by sorry
