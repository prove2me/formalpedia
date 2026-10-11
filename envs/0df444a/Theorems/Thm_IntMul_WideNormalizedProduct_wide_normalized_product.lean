-- Prove2me | Theorems.Thm_IntMul_WideNormalizedProduct_wide_normalized_product
-- name    : IntMul.WideNormalizedProduct.wide_normalized_product
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T16:18:44.392366+00:00
-- url     : https://prove2.me/theorems/1dde777e-b8e4-4836-8159-07dff90a4584
-- title:
--   Complete physical product recovery and exact requested width at any sufficient coefficient precision
-- statement:
--   From an explicit prepared convolution-coefficient frame, let $B=\operatorname{val}(z)+1$ and let $N=\operatorname{val}(l)+1$ be any sufficient coefficient precision, meaning $2B+\lceil\log_2\min(m_x,m_y)\rceil\le N$. A retained word $d$ specifies the requested product width $W=\operatorname{val}(d)+1=|x|+|y|$. The fixed sixteen-tape machine globally halts in its exact final frame and outputs exactly
--
--   $$\operatorname{bin}_W(\operatorname{val}(x)\operatorname{val}(y)).$$
--
--   Its actual transition bound is
--
--   $$(m_x+m_y)(41N+32B+21|z|+4|l|+126)+10W+6|d|+63.$$
--
--   This includes actual carry normalization, all reusable scratch cleanup, physical desired-width countdown preparation, output conversion and caller returns. Coefficient generation, coefficient loading and descriptor construction remain explicit upstream obligations.
-- source:
--   Original complete physical product output at arbitrary sufficient coefficient precision and exact requested width. Written by Codex.

import Definitions.Def_IntMul_WideNormalizedProduct
import Mathlib.Tactic
import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits

open IntMul IntMul.WideNormalizedProduct

theorem IntMul.WideNormalizedProduct.wide_normalized_product (base : machine.Cfg) (pre x y z l d : List Bool)
    (hl : CarryProduct.coefficientWidth (CarryStep.blockSize z) x y≤ val l+1)
    (hd : FixedOutputWidth.width d=x.length+y.length) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*(val l+1)+32*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+10*FixedOutputWidth.width d+6*d.length+63 ∧
      machine.step^[t] (initialFrame base pre x y z l d)=finalFrame base pre x y z l d ∧
      (machine.step^[t] (initialFrame base pre x y z l d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base pre x y z l d)).cells 1=
        machine.tapeOf ((bin (x.length+y.length) (val x*val y)).map machine.bitSym) := by sorry
