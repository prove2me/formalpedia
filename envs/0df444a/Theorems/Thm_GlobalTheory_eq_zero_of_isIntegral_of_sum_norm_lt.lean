-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_isIntegral_of_sum_norm_lt
-- name    : GlobalTheory.eq_zero_of_isIntegral_of_sum_norm_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:32.161516+00:00
-- url     : https://prove2.me/theorems/36ce417c-a762-4c90-b11b-9b0a92728caf
-- title:
--   Global Theory: eq zero of is Integral of sum norm lt
-- statement:
--   The Global Theory construction uses the eq zero of is Integral of sum norm lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L70-L73

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

theorem GlobalTheory.eq_zero_of_isIntegral_of_sum_norm_lt {x : K} (hx : IsIntegral ℤ x)
    (h : ∑ σ : K →+* ℂ, ‖σ x‖ < finrank ℚ K) : x = 0 := by sorry
