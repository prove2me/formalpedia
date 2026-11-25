-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_formAbsLe_iff
-- name    : GlobalTheory.HermFrame.formAbsLe_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:51.122736+00:00
-- url     : https://prove2.me/theorems/46799ef3-bf64-5c83-ac7a-112d150bd3ad
-- title:
--   Herm Frame: form Abs Le iff
-- statement:
--   The Herm Frame construction uses the form Abs Le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L584-L588
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L584-L588

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}

theorem GlobalTheory.HermFrame.formAbsLe_iff {V : Type*} {α β : V → V → ℂ} {C : ℝ} :
    FormAbsLe α C β ↔ ∀ ξ, |diagVal α ξ| ≤ C * diagVal β ξ := by sorry
