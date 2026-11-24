-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_summable_norm
-- name    : GlobalTheory.OpTrace.IsTraceClass.summable_norm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:44.836715+00:00
-- url     : https://prove2.me/theorems/c7f74f23-09ac-4265-b7f9-f03aa8059343
-- title:
--   Is Trace Class: summable norm
-- statement:
--   The Is Trace Class construction uses the summable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L172-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L172-L174

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

theorem GlobalTheory.OpTrace.IsTraceClass.summable_norm {T : H →L[ℂ] H} (h : IsTraceClass T) (e : HilbertBasis ι ℂ H) :
    Summable fun i => ‖⟪e i, T (e i)⟫_ℂ‖ := by sorry
