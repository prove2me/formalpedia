-- Prove2me | Theorems.Thm_GlobalTheory_trace_mem_of_mem_traceDual
-- name    : GlobalTheory.trace_mem_of_mem_traceDual
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:03.995087+00:00
-- url     : https://prove2.me/theorems/ea8e1bc3-9043-4058-afea-2e406042b945
-- title:
--   Global Theory: trace mem of mem trace Dual
-- statement:
--   The Global Theory construction uses the trace mem of mem trace Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L163-L167

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

theorem GlobalTheory.trace_mem_of_mem_traceDual {q : ℚ} (hq : q ≠ 0) {x : K}
    (hx : x ∈ Submodule.traceDual ℤ ℚ (Submodule.span (𝓞 K) {(q : K)})) :
    ∃ m : ℤ, Algebra.trace ℚ K x = q⁻¹ * m := by sorry
