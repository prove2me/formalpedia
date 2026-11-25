-- Prove2me | Theorems.Thm_GlobalTheory_finrank_div_rootDiscr_sq_le_sum_sq
-- name    : GlobalTheory.finrank_div_rootDiscr_sq_le_sum_sq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:07.553162+00:00
-- url     : https://prove2.me/theorems/d70d4dd6-b4a5-5cc3-8928-74a320065c4c
-- title:
--   Global Theory: finrank div root Discr sq le sum sq
-- statement:
--   The Global Theory construction uses the finrank div root Discr sq le sum sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L132-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L132-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {K : Type*} [Field K] [NumberField K]

theorem GlobalTheory.finrank_div_rootDiscr_sq_le_sum_sq {x : K}
    (hx : x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) / rootDiscr K ^ 2 ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by sorry
