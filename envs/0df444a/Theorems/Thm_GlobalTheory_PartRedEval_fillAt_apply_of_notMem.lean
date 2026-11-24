-- Prove2me | Theorems.Thm_GlobalTheory_PartRedEval_fillAt_apply_of_notMem
-- name    : GlobalTheory.PartRedEval.fillAt_apply_of_notMem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:17.914865+00:00
-- url     : https://prove2.me/theorems/b3ac56f6-0513-4e14-a94f-6c704a8ffcbe
-- title:
--   Part Red Eval: fill At apply of not Mem
-- statement:
--   The Part Red Eval construction uses the fill At apply of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEvaluateEntryOfMulLaw.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEvaluateEntryOfMulLaw.lean#L14-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRedEval
open GlobalTheory.PartRed
variable {k : Type} [Field k] {R Q : Type} [DecidableEq R] [DecidableEq Q]

theorem GlobalTheory.PartRedEval.fillAt_apply_of_notMem (β : Matrix R Q k) {E I : Finset (R × Q)} {e : R × Q} (hE : e ∉ E) (hI : e ∉ I)
    (x : Matrix R Q k) (y : I → k) : fillAt β E I x y e.1 e.2 = x e.1 e.2 := by sorry
