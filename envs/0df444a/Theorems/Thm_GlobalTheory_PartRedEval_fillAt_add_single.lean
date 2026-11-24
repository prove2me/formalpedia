-- Prove2me | Theorems.Thm_GlobalTheory_PartRedEval_fillAt_add_single
-- name    : GlobalTheory.PartRedEval.fillAt_add_single
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:34:36.435382+00:00
-- url     : https://prove2.me/theorems/cb21e89a-cbc5-4a52-b002-e12e9aa270b2
-- title:
--   Part Red Eval: fill At add single
-- statement:
--   The Part Red Eval construction uses the fill At add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEvaluateEntryOfMulLaw.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEvaluateEntryOfMulLaw.lean#L18-L27

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

theorem GlobalTheory.PartRedEval.fillAt_add_single (β : Matrix R Q k) {E I : Finset (R × Q)} {e : R × Q} (hE : e ∉ E) (hI : e ∉ I)
    (x : Matrix R Q k) (u : k) (y : I → k) :
    fillAt β E I (x + Matrix.single e.1 e.2 u) y = fillAt β E I x y + Matrix.single e.1 e.2 u := by sorry
