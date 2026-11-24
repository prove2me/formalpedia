-- Prove2me | Theorems.Thm_GlobalTheory_enorm_pow_mul_le_lintegral_circle
-- name    : GlobalTheory.enorm_pow_mul_le_lintegral_circle
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:50.885584+00:00
-- url     : https://prove2.me/theorems/2e60ba64-8d55-459c-a49c-0079f6e1583f
-- title:
--   Global Theory: enorm pow mul le lintegral circle
-- statement:
--   The Global Theory construction uses the enorm pow mul le lintegral circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L12-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L12-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ENNReal Real
open GlobalTheory
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

theorem GlobalTheory.enorm_pow_mul_le_lintegral_circle {f : ℂ → H} (hf : DiffContOnCl ℂ f (ball 0 1)) (n : ℕ) :
    ‖f 0‖ₑ ^ n * ENNReal.ofReal (2 * π) ≤
      ∫⁻ t in Ioc 0 (2 * π), ‖f (circleMap 0 1 t)‖ₑ ^ n := by sorry
