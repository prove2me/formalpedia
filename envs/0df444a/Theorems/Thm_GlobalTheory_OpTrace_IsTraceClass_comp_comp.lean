-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_comp_comp
-- name    : GlobalTheory.OpTrace.IsTraceClass.comp_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:21.037737+00:00
-- url     : https://prove2.me/theorems/3eb84418-8cda-44de-a093-5a52a72a5d36
-- title:
--   Is Trace Class: comp comp
-- statement:
--   The Is Trace Class construction uses the comp comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L232-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L232-L238

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

theorem GlobalTheory.OpTrace.IsTraceClass.comp_comp {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H →L[ℂ] K)
    (A' : K →L[ℂ] H) : IsTraceClass (A ∘L T ∘L A') := by sorry
