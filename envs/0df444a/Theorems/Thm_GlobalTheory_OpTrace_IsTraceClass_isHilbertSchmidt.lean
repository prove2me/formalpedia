-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_isHilbertSchmidt
-- name    : GlobalTheory.OpTrace.IsTraceClass.isHilbertSchmidt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:56.336003+00:00
-- url     : https://prove2.me/theorems/425ceae6-525f-4616-883d-d008cd3a1981
-- title:
--   Is Trace Class: is Hilbert Schmidt
-- statement:
--   The Is Trace Class construction uses the is Hilbert Schmidt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L255-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L255-L259

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

theorem GlobalTheory.OpTrace.IsTraceClass.isHilbertSchmidt {T : H →L[ℂ] H} (h : IsTraceClass T) :
    IsHilbertSchmidt T := by sorry
