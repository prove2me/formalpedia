-- Prove2me | Theorems.Thm_GlobalTheory_norm_pow_mul_integral_ball_le
-- name    : GlobalTheory.norm_pow_mul_integral_ball_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:12:48.649743+00:00
-- url     : https://prove2.me/theorems/f598fc64-5978-4564-b16d-32ad89ae4289
-- title:
--   Global Theory: norm pow mul integral ball le
-- statement:
--   The Global Theory construction uses the norm pow mul integral ball le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L179-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L179-L193

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

theorem GlobalTheory.norm_pow_mul_integral_ball_le (μ : Measure E) [μ.IsAddHaarMeasure] {a : E}
    {r : ℝ} {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball a r)) {w : ℝ → ℝ}
    (hw : Measurable w) (hw0 : ∀ t, 0 ≤ t → 0 ≤ w t) (n : ℕ)
    (hi : IntegrableOn (fun z => w ‖z - a‖) (ball a r) μ)
    (hi' : IntegrableOn (fun z => ‖φ z‖ ^ n * w ‖z - a‖) (ball a r) μ) :
    ‖φ a‖ ^ n * ∫ z in ball a r, w ‖z - a‖ ∂μ ≤ ∫ z in ball a r, ‖φ z‖ ^ n * w ‖z - a‖ ∂μ := by sorry
