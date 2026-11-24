-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_curv_eq
-- name    : GlobalTheory.HermFrame.curv_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:38:24.456626+00:00
-- url     : https://prove2.me/theorems/127a21ca-1f22-4847-84f2-d69ab8d83619
-- title:
--   Herm Frame: curv eq
-- statement:
--   The Herm Frame construction uses the curv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L420-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L420-L429

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
variable {U : Set E} {H H' : E → Matrix n n ℂ} {z : E} {j k : WithTop ℕ∞}

theorem GlobalTheory.HermFrame.curv_eq (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : E) :
    curv H z ξ η = (H z)ᵀ⁻¹ * (mdbar H z η)ᵀ * (H z)ᵀ⁻¹ * (mdel H z ξ)ᵀ
      - (H z)ᵀ⁻¹ * (mddbar H z ξ η)ᵀ := by sorry
