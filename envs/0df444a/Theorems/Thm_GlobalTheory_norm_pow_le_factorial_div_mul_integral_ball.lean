-- Prove2me | Theorems.Thm_GlobalTheory_norm_pow_le_factorial_div_mul_integral_ball
-- name    : GlobalTheory.norm_pow_le_factorial_div_mul_integral_ball
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:07.393797+00:00
-- url     : https://prove2.me/theorems/a4199c47-6ea3-45e7-93e7-5ab20e024554
-- title:
--   Global Theory: norm pow le factorial div mul integral ball
-- statement:
--   The Global Theory construction uses the norm pow le factorial div mul integral ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L260-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L260-L267

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

theorem GlobalTheory.norm_pow_le_factorial_div_mul_integral_ball {a : E} {r : ℝ} (hr : 0 < r) {φ : E → H}
    (hφ : DifferentiableOn ℂ φ (ball a r)) (n : ℕ)
    (hi : IntegrableOn (fun z => ‖φ z‖ ^ n) (ball a r)) :
    ‖φ a‖ ^ n ≤ (Module.finrank ℂ E).factorial /
      (π ^ Module.finrank ℂ E * r ^ (2 * Module.finrank ℂ E)) * ∫ z in ball a r, ‖φ z‖ ^ n := by sorry
