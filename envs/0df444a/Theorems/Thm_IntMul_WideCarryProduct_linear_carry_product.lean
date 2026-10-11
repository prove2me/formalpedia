-- Prove2me | Theorems.Thm_IntMul_WideCarryProduct_linear_carry_product
-- name    : IntMul.WideCarryProduct.linear_carry_product
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T16:06:35.251843+00:00
-- url     : https://prove2.me/theorems/de575e43-e314-4c19-9efe-05d3b80c80b1
-- title:
--   Linear actual transition cost of logarithmic-block physical product recovery
-- statement:
--   Let $W=|x|+|y|>0$, $B=\lg W$, and $N=3B$. Suppose the actual block-size-minus-one and precision-minus-one words $z,l$ satisfy $|z|\le B$ and $|l|\le3B$. From the explicit prepared convolution-coefficient frame, the fifteen-tape physical carry/output machine halts in its exact terminal frame within
--
--   $$909W+21$$
--
--   actual transitions. Its output is the exact product padded to $B(m_x+m_y)$ bits, and its final carry bank contains the canonical $N$-bit zero word. Every framed coefficient read, binary addition, carry propagation, scratch cleanup, output reversal and caller return is included. Coefficient generation, loading, global initialization and requested-width conversion remain upstream or downstream stages.
-- source:
--   Original explicit linear clock bound for physical carry product recovery at logarithmic block size. Written by Codex.

import Definitions.Def_IntMul_WideCarryProduct
import Mathlib.Tactic

open IntMul IntMul.WideCarryProduct

theorem IntMul.WideCarryProduct.linear_carry_product (pre x y z l : List Bool)
    (hW : 0< x.length+y.length)
    (hB : CarryStep.blockSize z=lg (x.length+y.length))
    (hN : val l+1=3*CarryStep.blockSize z)
    (hz : z.length≤ CarryStep.blockSize z)
    (hl : l.length≤ 3*CarryStep.blockSize z) :
    ∃ t : ℕ,
      t ≤ 909*(x.length+y.length)+21 ∧
      machine.step^[t] (initialFrame pre x y z l)=finalFrame pre x y z l ∧
      (machine.step^[t] (initialFrame pre x y z l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 1=
        machine.tapeOf ((bin (CarryStep.blockSize z*
          (DigitConvolution.blockCount (CarryStep.blockSize z) x+
            DigitConvolution.blockCount (CarryStep.blockSize z) y)) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 12=
        machine.tapeOf ((bin ((val l+1)) 0).map machine.bitSym) := by sorry
