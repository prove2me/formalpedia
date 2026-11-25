-- Prove2me | Theorems.Thm_GlobalTheory_finrank_le_trace_of_isIntegral
-- name    : GlobalTheory.finrank_le_trace_of_isIntegral
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:50:41.953558+00:00
-- url     : https://prove2.me/theorems/83e6cf44-5f19-4c98-9235-adc397abd5a4
-- title:
--   Global Theory: finrank le trace of is Integral
-- statement:
--   The Global Theory construction uses the finrank le trace of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L236-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L236-L241

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

theorem GlobalTheory.finrank_le_trace_of_isIntegral {a : F} (hi : IsIntegral ℤ a)
    (ha : ∀ σ : F →+* ℝ, 0 < σ a) : (finrank ℚ F : ℚ) ≤ Algebra.trace ℚ F a := by sorry
