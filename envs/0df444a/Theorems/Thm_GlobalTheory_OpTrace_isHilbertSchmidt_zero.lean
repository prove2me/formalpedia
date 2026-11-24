-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_isHilbertSchmidt_zero
-- name    : GlobalTheory.OpTrace.isHilbertSchmidt_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:15.970034+00:00
-- url     : https://prove2.me/theorems/07153055-464b-4ed2-901d-a6045d711517
-- title:
--   Op Trace: is Hilbert Schmidt zero
-- statement:
--   The Op Trace construction uses the is Hilbert Schmidt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L102-L103

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
omit [CompleteSpace K]

theorem GlobalTheory.OpTrace.isHilbertSchmidt_zero : IsHilbertSchmidt (0 : H →L[ℂ] K) := by sorry
