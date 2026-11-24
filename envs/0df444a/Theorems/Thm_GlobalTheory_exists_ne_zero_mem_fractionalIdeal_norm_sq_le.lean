-- Prove2me | Theorems.Thm_GlobalTheory_exists_ne_zero_mem_fractionalIdeal_norm_sq_le
-- name    : GlobalTheory.exists_ne_zero_mem_fractionalIdeal_norm_sq_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:36:34.352025+00:00
-- url     : https://prove2.me/theorems/26cdd0f0-1b3e-4e56-94a2-3b11cff5beb2
-- title:
--   Global Theory: exists ne zero mem fractional Ideal norm sq le
-- statement:
--   The Global Theory construction uses the exists ne zero mem fractional Ideal norm sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroMemFractionalIdealNormSqLe.lean#L60-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroMemFractionalIdealNormSqLe.lean#L60-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped nonZeroDivisors NNReal ENNReal
variable {E : Type*} [Field E] [NumberField E] [IsTotallyComplex E] {f : ℕ}

theorem GlobalTheory.exists_ne_zero_mem_fractionalIdeal_norm_sq_le (hf : finrank ℚ E = 2 * f)
    (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0) :
    ∃ a ∈ J, a ≠ 0 ∧ ∀ τ : E →+* ℂ, ‖τ a‖ ^ 2 ≤
      2 / Real.pi * ((FractionalIdeal.absNorm J : ℝ) * √|(discr E : ℝ)|) ^ ((f : ℝ)⁻¹) := by sorry
