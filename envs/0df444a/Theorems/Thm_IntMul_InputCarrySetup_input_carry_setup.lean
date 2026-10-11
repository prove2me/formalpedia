-- Prove2me | Theorems.Thm_IntMul_InputCarrySetup_input_carry_setup
-- name    : IntMul.InputCarrySetup.input_carry_setup
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T17:31:13.718952+00:00
-- url     : https://prove2.me/theorems/a4d9a6c2-99d4-43df-9125-440e4a9d4498
-- title:
--   Complete linear-time physical parameter and zero-carry setup from original multiplication input
-- statement:
--   Let $x,y$ be finite binary operands with total width $W=|x|+|y|>0$ and $B=\max(\lceil\log_2 W\rceil,1)$. One fixed eighteen-tape finite machine, starting from its genuine initial $x\#y$ configuration with blank work tapes and all heads at zero, reaches its exact globally halted preparation frame within
--
--   $$85W+109$$
--
--   actual transitions. It retains the input, leaves global output empty, computes canonical retained descriptors for $W-1$, $B-1$, and $3B-1$, prepares their stated countdown/template banks physically, and generates the exact zero carry $\operatorname{bin}_{3B}(0)$ on bank 12 with head at zero. The three retained descriptor heads are at zero and the original input cursor is at its end blank. The precision $3B$ is sufficient for every convolution coefficient and carry-normalization sum. Fast coefficient production and copying the block descriptor into its final arithmetic bank remain separate stages.
-- source:
--   Original complete physical linear-time input-derived parameter and zero-carry preparation. Written by Codex.

import Definitions.Def_IntMul_InputCarrySetup
import Mathlib.Tactic
import Definitions.Def_IntMul_CarryProduct

open IntMul IntMul.InputCarrySetup

theorem IntMul.InputCarrySetup.input_carry_setup (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 85*(x.length+y.length)+109 ∧
      machine.step^[t] (machine.initCfg x y)=finalFrame x y ∧
      (machine.step^[t] (machine.initCfg x y)).state=machine.qHalt ∧
      (machine.step^[t] (machine.initCfg x y)).cells machine.inTape=(machine.initCfg x y).cells machine.inTape ∧
      (machine.step^[t] (machine.initCfg x y)).cells machine.outTape=machine.tapeOf [] ∧
      (machine.step^[t] (machine.initCfg x y)).cells 12=
        machine.tapeOf ((bin (3*lg (x.length+y.length)) 0).map machine.bitSym) ∧
      (machine.step^[t] (machine.initCfg x y)).head 12=0 ∧
      (machine.step^[t] (machine.initCfg x y)).head machine.inTape=x.length+y.length+2 ∧
      (∀ i : Fin 18, i.val=15 ∨ i.val=16 ∨ i.val=17 →
        (machine.step^[t] (machine.initCfg x y)).head i=0) ∧
      val (InputArithmeticDescriptors.widthWord x y)+1=x.length+y.length ∧
      val (InputArithmeticDescriptors.blockWord x y)+1=lg (x.length+y.length) ∧
      val (InputArithmeticDescriptors.precisionWord x y)+1=3*lg (x.length+y.length) ∧
      CarryProduct.coefficientWidth (lg (x.length+y.length)) x y≤ 3*lg (x.length+y.length) := by sorry
