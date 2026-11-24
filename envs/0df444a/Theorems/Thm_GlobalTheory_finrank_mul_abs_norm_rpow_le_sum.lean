-- Prove2me | Theorems.Thm_GlobalTheory_finrank_mul_abs_norm_rpow_le_sum
-- name    : GlobalTheory.finrank_mul_abs_norm_rpow_le_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:06.002891+00:00
-- url     : https://prove2.me/theorems/39fa43b8-23a6-43a5-af71-b5119f2aa9c1
-- title:
--   Global Theory: finrank mul abs norm rpow le sum
-- statement:
--   The Global Theory construction uses the finrank mul abs norm rpow le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L39-L43

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

theorem GlobalTheory.finrank_mul_abs_norm_rpow_le_sum (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ ((finrank ℚ K : ℝ)⁻¹)
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ := by sorry
