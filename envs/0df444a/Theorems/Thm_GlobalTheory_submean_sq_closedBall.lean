-- Prove2me | Theorems.Thm_GlobalTheory_submean_sq_closedBall
-- name    : GlobalTheory.submean_sq_closedBall
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:39.709822+00:00
-- url     : https://prove2.me/theorems/ac10a1ae-d11e-5515-8385-448c5791e65c
-- title:
--   Global Theory: submean sq closed Ball
-- statement:
--   The Global Theory construction uses the submean sq closed Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L349-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L349-L367

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

theorem GlobalTheory.submean_sq_closedBall {D : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] {r : ℝ} (hr : 0 < r) {φ : EuclideanSpace ℂ (Fin D) → H}
    (hφ : DifferentiableOn ℂ φ (ball 0 r)) :
    (∀ w : ℝ → ℝ≥0∞, Measurable w →
      ‖φ 0‖ₑ ^ 2 * ∫⁻ z in closedBall (0 : EuclideanSpace ℂ (Fin D)) r, w ‖z‖ ≤
        ∫⁻ z in closedBall (0 : EuclideanSpace ℂ (Fin D)) r, ‖φ z‖ₑ ^ 2 * w ‖z‖) ∧
    ‖φ 0‖ₑ ^ 2 ≤ (volume (closedBall (0 : EuclideanSpace ℂ (Fin D)) r))⁻¹ *
      ∫⁻ z in closedBall (0 : EuclideanSpace ℂ (Fin D)) r, ‖φ z‖ₑ ^ 2 ∧
    volume (closedBall (0 : EuclideanSpace ℂ (Fin D)) r) =
      ENNReal.ofReal (π ^ D * r ^ (2 * D) / D.factorial) := by sorry
