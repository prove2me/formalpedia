-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_isIntegral_of_sum_abs_lt
-- name    : GlobalTheory.eq_zero_of_isIntegral_of_sum_abs_lt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:05.257342+00:00
-- url     : https://prove2.me/theorems/2b524368-77c4-447e-ba68-1833bd230a26
-- title:
--   Global Theory: eq zero of is Integral of sum abs lt
-- statement:
--   The Global Theory construction uses the eq zero of is Integral of sum abs lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L243-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L243-L245

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
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]

theorem GlobalTheory.eq_zero_of_isIntegral_of_sum_abs_lt {x : F} (hx : IsIntegral ℤ x)
    (h : ∑ σ : F →+* ℝ, |σ x| < finrank ℚ F) : x = 0 := by sorry
