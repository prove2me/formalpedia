-- Prove2me | Theorems.Thm_GlobalTheory_trace_mem_of_mem_dual_spanSingleton
-- name    : GlobalTheory.trace_mem_of_mem_dual_spanSingleton
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:32.84918+00:00
-- url     : https://prove2.me/theorems/5b77b5d2-c356-45db-a717-a410e0673670
-- title:
--   Global Theory: trace mem of mem dual span Singleton
-- statement:
--   The Global Theory construction uses the trace mem of mem dual span Singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L169-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L169-L176

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

theorem GlobalTheory.trace_mem_of_mem_dual_spanSingleton {q : ℚ} (hq : q ≠ 0) {x : K}
    (hx : x ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.spanSingleton (𝓞 K)⁰ (q : K))) :
    ∃ m : ℤ, Algebra.trace ℚ K x = q⁻¹ * m := by sorry
