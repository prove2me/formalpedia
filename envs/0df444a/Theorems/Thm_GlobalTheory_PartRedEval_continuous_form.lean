-- Prove2me | Theorems.Thm_GlobalTheory_PartRedEval_continuous_form
-- name    : GlobalTheory.PartRedEval.continuous_form
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:35:11.633335+00:00
-- url     : https://prove2.me/theorems/1b49171a-fc2e-4890-9169-b49c6ade26d6
-- title:
--   Part Red Eval: continuous form
-- statement:
--   The Part Red Eval construction uses the continuous form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEvaluateEntryOfMulLaw.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEvaluateEntryOfMulLaw.lean#L46-L55

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]

theorem GlobalTheory.PartRedEval.continuous_form (w : Matrix R Q k →ₗ[k] k) : Continuous w := by sorry
