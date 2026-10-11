-- Prove2me | Theorems.Thm_IntMul_BankedProduct_banked_product
-- name    : IntMul.BankedProduct.banked_product
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T14:18:33.583828+00:00
-- url     : https://prove2.me/theorems/960dc13a-f0e3-43c0-8ed7-4a443775a452
-- title:
--   Complete writable-bank product normalization with global output return and retained original input
-- statement:
--   Let $x,y,z,l,d$ be finite binary words. Put $B=\operatorname{val}(z)+1$, let $m_x,m_y$ be the base-$2^B$ operand block counts, put $N=2B+\lceil\log_2\min(m_x,m_y)\rceil$ with the natural-number zero convention, and $W=\operatorname{val}(d)+1=|x|+|y|$. Assume $\operatorname{val}(l)+1=N$. A fixed eighteen-tape machine starts from the explicit physically prepared work-bank frame containing the padded product convolution coefficients, zero carry and retained descriptors. It halts in the exact returned global caller configuration within
--
--   $$(m_x+m_y)(41N+32B+21|z|+4|l|+126)+12W+6|d|+67$$
--
--   actual transitions, with global output exactly the big-endian $W$-bit representation of $\operatorname{val}(x)\operatorname{val}(y)$. The true original caller input tape and head and every cell-zero work-bank prefix are retained. Product arithmetic, descriptor preparation, width conversion, every native caller return, the physical child-output rewind, bit-by-bit global return and final halt are all charged. The coefficient input is a writable physical work bank; preparing the incoming coefficients, descriptors, local bank markers and cursors remains an explicit caller obligation.
-- source:
--   Original complete composition of physical product normalization with arbitrary-prepared-state banked execution. Owns native marker proofs, exact terminal output-head identity, physical caller instantiation, complete product frame and clock. Written by Codex.

import Definitions.Def_IntMul_BankedProduct
import Mathlib.Tactic

open IntMul IntMul.BankedProduct

theorem IntMul.BankedProduct.banked_product (base : machine.Cfg) (nativeBase : child.Cfg)
    (pre x y z l d : List Bool)
    (hl : val l+1=CarryProduct.coefficientWidth (CarryStep.blockSize z) x y)
    (hd : FixedOutputWidth.width d=x.length+y.length) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*CarryProduct.coefficientWidth (CarryStep.blockSize z) x y+32*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+12*FixedOutputWidth.width d+6*d.length+67 ∧
      machine.step^[t] (initialFrame base nativeBase pre x y z l d)=finalFrame base nativeBase pre x y z l d ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells machine.outTape=
        machine.tapeOf ((bin (x.length+y.length) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).head machine.inTape=base.head machine.inTape ∧
      (∀ j, (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells (BankedSimulation.workTape child j) 0=
        base.cells (BankedSimulation.workTape child j) 0) := by sorry
