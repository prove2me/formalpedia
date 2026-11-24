-- Prove2me | Theorems.Thm_GlobalTheory_enorm_pow_mul_lintegral_ball_le_of_centre
-- name    : GlobalTheory.enorm_pow_mul_lintegral_ball_le_of_centre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:47.5938+00:00
-- url     : https://prove2.me/theorems/694b9151-515e-463c-90a6-0ff31a4ce0dc
-- title:
--   Global Theory: enorm pow mul lintegral ball le of centre
-- statement:
--   The Global Theory construction uses the enorm pow mul lintegral ball le of centre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L150-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L150-L165

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

theorem GlobalTheory.enorm_pow_mul_lintegral_ball_le_of_centre (μ : Measure E) [μ.IsAddHaarMeasure] {a : E}
    {r : ℝ} {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball a r)) {w : ℝ → ℝ≥0∞}
    (hw : Measurable w) (n : ℕ) :
    ‖φ a‖ₑ ^ n * ∫⁻ z in ball a r, w ‖z - a‖ ∂μ ≤
      ∫⁻ z in ball a r, ‖φ z‖ₑ ^ n * w ‖z - a‖ ∂μ := by sorry
