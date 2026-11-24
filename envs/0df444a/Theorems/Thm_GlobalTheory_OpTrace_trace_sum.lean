-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_trace_sum
-- name    : GlobalTheory.OpTrace.trace_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:41.502708+00:00
-- url     : https://prove2.me/theorems/56e55d8b-60d8-4f67-b6a8-31d82cf5494a
-- title:
--   Op Trace: trace sum
-- statement:
--   The Op Trace construction uses the trace sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L268-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L268-L271

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  {ι κ : Type*}

theorem GlobalTheory.OpTrace.trace_sum {α : Type*} (s : Finset α) {T : α → (H →L[ℂ] H)}
    (h : ∀ a ∈ s, IsTraceClass (T a)) : trace (∑ a ∈ s, T a) = ∑ a ∈ s, trace (T a) := by sorry
