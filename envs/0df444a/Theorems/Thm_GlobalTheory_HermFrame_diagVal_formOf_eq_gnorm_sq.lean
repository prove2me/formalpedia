-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_diagVal_formOf_eq_gnorm_sq
-- name    : GlobalTheory.HermFrame.diagVal_formOf_eq_gnorm_sq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:06.983288+00:00
-- url     : https://prove2.me/theorems/9e80268f-6c8d-4e6a-92ed-4f8c1fc09007
-- title:
--   Herm Frame: diag Val form Of eq gnorm sq
-- statement:
--   The Herm Frame construction uses the diag Val form Of eq gnorm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L600-L601
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L600-L601

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
variable {ι : Type*} [Fintype ι]

theorem GlobalTheory.HermFrame.diagVal_formOf_eq_gnorm_sq {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (ξ : ι → ℂ) :
    diagVal (formOf G) ξ = gnorm G ξ ^ 2 := by sorry
