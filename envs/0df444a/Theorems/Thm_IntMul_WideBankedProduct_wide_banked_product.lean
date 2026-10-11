-- Prove2me | Theorems.Thm_IntMul_WideBankedProduct_wide_banked_product
-- name    : IntMul.WideBankedProduct.wide_banked_product
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T16:27:41.707046+00:00
-- url     : https://prove2.me/theorems/13b87415-2ed4-4679-b2fc-4b61c325f294
-- title:
--   Complete writable-bank exact product output at arbitrary sufficient coefficient precision
-- statement:
--   Let $B=\operatorname{val}(z)+1$, $N=\operatorname{val}(l)+1$ be any sufficient coefficient precision, and $W=\operatorname{val}(d)+1=|x|+|y|$. From the explicit physically prepared work-bank frame containing the convolution coefficients, zero carry, retained descriptors and local markers, a fixed eighteen-tape machine globally halts in its exact returned caller configuration within
--
--   $$(m_x+m_y)(41N+32B+21|z|+4|l|+126)+12W+6|d|+67$$
--
--   actual transitions. Global output is exactly the $W$-bit product representation. The original global input cells and head, every bank prefix and the complete terminal native bank frame are retained. All arithmetic, width preparation, exact width conversion, native returns, physical output rewind and bit-by-bit global return are charged. Coefficient generation, loading and preparing the incoming banks remain explicit caller obligations.
-- source:
--   Original complete physical writable-bank product recovery for any sufficient coefficient precision. Written by Codex.

import Definitions.Def_IntMul_WideBankedProduct
import Mathlib.Tactic

open IntMul IntMul.WideBankedProduct

theorem IntMul.WideBankedProduct.wide_banked_product (base : machine.Cfg) (nativeBase : child.Cfg)
    (pre x y z l d : List Bool)
    (hl : CarryProduct.coefficientWidth (CarryStep.blockSize z) x y≤ val l+1)
    (hd : FixedOutputWidth.width d=x.length+y.length) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*(val l+1)+32*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+12*FixedOutputWidth.width d+6*d.length+67 ∧
      machine.step^[t] (initialFrame base nativeBase pre x y z l d)=finalFrame base nativeBase pre x y z l d ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells machine.outTape=
        machine.tapeOf ((bin (x.length+y.length) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).head machine.inTape=base.head machine.inTape ∧
      (∀ j, (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells (BankedSimulation.workTape child j) 0=
        base.cells (BankedSimulation.workTape child j) 0) := by sorry
