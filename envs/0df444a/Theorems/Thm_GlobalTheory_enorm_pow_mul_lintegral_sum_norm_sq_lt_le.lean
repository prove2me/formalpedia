-- Prove2me | Theorems.Thm_GlobalTheory_enorm_pow_mul_lintegral_sum_norm_sq_lt_le
-- name    : GlobalTheory.enorm_pow_mul_lintegral_sum_norm_sq_lt_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:44:27.197509+00:00
-- url     : https://prove2.me/theorems/9e798a2d-e634-5ec9-8e69-76e0cb95120c
-- title:
--   Global Theory: enorm pow mul lintegral sum norm sq lt le
-- statement:
--   The Global Theory construction uses the enorm pow mul lintegral sum norm sq lt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L332-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L332-L347

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
variable {ι : Type*} [Fintype ι]

theorem GlobalTheory.enorm_pow_mul_lintegral_sum_norm_sq_lt_le {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [CompleteSpace H] {R : ℝ} {φ : (ι → ℂ) → H}
    (hφ : DifferentiableOn ℂ φ {x | ∑ i, ‖x i‖ ^ 2 < R}) {w : ℝ → ℝ≥0∞} (hw : Measurable w)
    (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < R}, w (∑ i, ‖z i‖ ^ 2) ≤
      ∫⁻ z in {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < R}, ‖φ z‖ₑ ^ n * w (∑ i, ‖z i‖ ^ 2) := by sorry
