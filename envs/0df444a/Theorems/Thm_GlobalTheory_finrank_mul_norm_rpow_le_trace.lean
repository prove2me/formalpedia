-- Prove2me | Theorems.Thm_GlobalTheory_finrank_mul_norm_rpow_le_trace
-- name    : GlobalTheory.finrank_mul_norm_rpow_le_trace
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:50:45.191798+00:00
-- url     : https://prove2.me/theorems/7d77b6d4-096e-4af0-a6d3-aaa667029e72
-- title:
--   Global Theory: finrank mul norm rpow le trace
-- statement:
--   The Global Theory construction uses the finrank mul norm rpow le trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L226-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L226-L234

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

theorem GlobalTheory.finrank_mul_norm_rpow_le_trace {a : F} (ha : ∀ σ : F →+* ℝ, 0 < σ a) :
    (finrank ℚ F : ℝ) * ((Algebra.norm ℚ a : ℚ) : ℝ) ^ (1 / (finrank ℚ F : ℝ))
      ≤ ((Algebra.trace ℚ F a : ℚ) : ℝ) := by sorry
