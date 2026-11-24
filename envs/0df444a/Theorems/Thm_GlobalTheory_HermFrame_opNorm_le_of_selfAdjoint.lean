-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_opNorm_le_of_selfAdjoint
-- name    : GlobalTheory.HermFrame.opNorm_le_of_selfAdjoint
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:19:38.486689+00:00
-- url     : https://prove2.me/theorems/9dae1dfb-c420-4d26-8b03-646f73b1c101
-- title:
--   Herm Frame: op Norm le of self Adjoint
-- statement:
--   The Herm Frame construction uses the op Norm le of self Adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L224-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L224-L253

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable {H : Matrix m m ℂ} {K : Matrix n n ℂ} {L : Matrix l l ℂ}

theorem GlobalTheory.HermFrame.opNorm_le_of_selfAdjoint (hH : H.PosSemidef) {T : Matrix m m ℂ}
    (hT : ∀ v w, form H (T *ᵥ v) w = form H v (T *ᵥ w)) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, ‖form H (T *ᵥ v) v‖ ≤ c * gnorm H v ^ 2) : opNorm H H T ≤ c := by sorry
