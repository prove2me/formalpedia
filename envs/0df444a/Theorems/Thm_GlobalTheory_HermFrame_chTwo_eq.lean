-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_chTwo_eq
-- name    : GlobalTheory.HermFrame.chTwo_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:05.885133+00:00
-- url     : https://prove2.me/theorems/eb1e6a8c-81f9-4457-bf77-8f6eb1c69a59
-- title:
--   Herm Frame: ch Two eq
-- statement:
--   The Herm Frame construction uses the ch Two eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L716-L725
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L716-L725

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
variable [Fintype n] [DecidableEq n]

theorem GlobalTheory.HermFrame.chTwo_eq (H : E → Matrix n n ℂ) (z ξ₁ η₁ ξ₂ η₂ : E) :
    chTwo H z ξ₁ η₁ ξ₂ η₂ =
      (wedge (chernOne H z) (chernOne H z) ξ₁ η₁ ξ₂ η₂ - 2 * chernTwo H z ξ₁ η₁ ξ₂ η₂) / 2 := by sorry
