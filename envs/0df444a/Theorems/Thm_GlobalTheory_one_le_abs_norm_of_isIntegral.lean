-- Prove2me | Theorems.Thm_GlobalTheory_one_le_abs_norm_of_isIntegral
-- name    : GlobalTheory.one_le_abs_norm_of_isIntegral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:52.83913+00:00
-- url     : https://prove2.me/theorems/6d88b820-1388-4531-aa4b-beb27c6457ba
-- title:
--   Global Theory: one le abs norm of is Integral
-- statement:
--   The Global Theory construction uses the one le abs norm of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L52-L61

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

theorem GlobalTheory.one_le_abs_norm_of_isIntegral {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    1 ≤ |Algebra.norm ℚ x| := by sorry
