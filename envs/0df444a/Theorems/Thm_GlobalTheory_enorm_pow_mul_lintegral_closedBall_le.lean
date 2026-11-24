-- Prove2me | Theorems.Thm_GlobalTheory_enorm_pow_mul_lintegral_closedBall_le
-- name    : GlobalTheory.enorm_pow_mul_lintegral_closedBall_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:16:19.072822+00:00
-- url     : https://prove2.me/theorems/af9620e6-8a25-4fb5-af74-98f78a9f79ca
-- title:
--   Global Theory: enorm pow mul lintegral closed Ball le
-- statement:
--   The Global Theory construction uses the enorm pow mul lintegral closed Ball le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L136-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L136-L148

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

theorem GlobalTheory.enorm_pow_mul_lintegral_closedBall_le (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ}
    {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball 0 r)) {w : ℝ → ℝ≥0∞} (hw : Measurable w) (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in closedBall 0 r, w ‖z‖ ∂μ ≤
      ∫⁻ z in closedBall 0 r, ‖φ z‖ₑ ^ n * w ‖z‖ ∂μ := by sorry
