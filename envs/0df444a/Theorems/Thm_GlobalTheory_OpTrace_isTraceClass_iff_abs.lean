-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_isTraceClass_iff_abs
-- name    : GlobalTheory.OpTrace.isTraceClass_iff_abs
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:52.884651+00:00
-- url     : https://prove2.me/theorems/ac2e9f13-0372-48ca-8bca-87ab85546f92
-- title:
--   Op Trace: is Trace Class iff abs
-- statement:
--   The Op Trace construction uses the is Trace Class iff abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L296-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L296-L315

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

theorem GlobalTheory.OpTrace.isTraceClass_iff_abs (e : HilbertBasis ι ℂ H) {T : H →L[ℂ] H} :
    IsTraceClass T ↔ Summable fun i => ⟪e i, CFC.abs T (e i)⟫_ℂ := by sorry
