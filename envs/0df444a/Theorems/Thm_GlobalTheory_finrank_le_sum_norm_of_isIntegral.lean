-- Prove2me | Theorems.Thm_GlobalTheory_finrank_le_sum_norm_of_isIntegral
-- name    : GlobalTheory.finrank_le_sum_norm_of_isIntegral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:10.407989+00:00
-- url     : https://prove2.me/theorems/2f84c2bf-e684-40ba-b586-da0efd4ca10a
-- title:
--   Global Theory: finrank le sum norm of is Integral
-- statement:
--   The Global Theory construction uses the finrank le sum norm of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L63-L68

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

theorem GlobalTheory.finrank_le_sum_norm_of_isIntegral {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) ≤ ∑ σ : K →+* ℂ, ‖σ x‖ := by sorry
