-- Prove2me | Theorems.Thm_IntMul_InputParameterBanks_setup_parameters
-- name    : IntMul.InputParameterBanks.setup_parameters
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T18:01:29.391611+00:00
-- url     : https://prove2.me/theorems/7768076d-b03c-48a3-8d2f-816ae8611ca1
-- title:
--   Complete linear-time parameter banks and zero carry from original multiplication input
-- statement:
--   Let $x,y$ be finite binary operands with total width $W=|x|+|y|>0$ and $B=\max(\lceil\log_2 W\rceil,1)$. One fixed eighteen-tape finite machine, starting from its genuine initial $x\#y$ configuration with blank work tapes and all heads at zero, reaches its exact globally halted preparation frame within
--
--   $$87W+114$$
--
--   actual transitions. It retains the input, leaves global output empty, computes canonical retained descriptors for $W-1$, $B-1$, and $3B-1$, prepares their stated countdown/template banks physically, and generates the exact zero carry $\operatorname{bin}_{3B}(0)$ on bank 12 with head at zero. The three retained descriptor heads are at zero and the original input cursor is at its end blank. The precision $3B$ is sufficient for every convolution coefficient and carry-normalization sum. The block descriptor is physically copied to arithmetic bank 6 and both source and destination heads are returned to zero. Fast coefficient production and bank/local-marker integration remain separate stages.
-- source:
--   Original complete physical linear-time input-derived parameter and zero-carry preparation. Written by Codex.

import Definitions.Def_IntMul_CarryProduct
import Definitions.Def_IntMul_InputParameterBanks
import Mathlib.Tactic

open IntMul IntMul.InputParameterBanks

theorem IntMul.InputParameterBanks.setup_parameters (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 87*(x.length+y.length)+114 ∧
      machine.step^[t] (machine.initCfg x y)=finalFrame x y ∧
      (machine.step^[t] (machine.initCfg x y)).state=machine.qHalt ∧
      (machine.step^[t] (machine.initCfg x y)).cells machine.inTape=(machine.initCfg x y).cells machine.inTape ∧
      (machine.step^[t] (machine.initCfg x y)).cells machine.outTape=machine.tapeOf [] ∧
      (machine.step^[t] (machine.initCfg x y)).cells 6=
        machine.tapeOf ((InputArithmeticDescriptors.blockWord x y).map machine.bitSym) ∧
      (machine.step^[t] (machine.initCfg x y)).head 6=0 ∧
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
