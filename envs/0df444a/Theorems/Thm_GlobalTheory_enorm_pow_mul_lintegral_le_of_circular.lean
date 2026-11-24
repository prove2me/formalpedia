-- Prove2me | Theorems.Thm_GlobalTheory_enorm_pow_mul_lintegral_le_of_circular
-- name    : GlobalTheory.enorm_pow_mul_lintegral_le_of_circular
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:16:39.882812+00:00
-- url     : https://prove2.me/theorems/1d439fcb-be66-4917-9100-2e63f9239a4a
-- title:
--   Global Theory: enorm pow mul lintegral le of circular
-- statement:
--   The Global Theory construction uses the enorm pow mul lintegral le of circular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L72-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L72-L114

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

theorem GlobalTheory.enorm_pow_mul_lintegral_le_of_circular (μ : Measure E) [μ.IsAddHaarMeasure] {S : Set E}
    (hS : MeasurableSet S) (hSc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z ∈ S, c • z ∈ S) {φ : E → H}
    (hφc : ContinuousOn φ S) (hφ : ∀ z ∈ S, DiffContOnCl ℂ (fun c : ℂ => φ (c • z)) (ball 0 1))
    {w : E → ℝ≥0∞} (hw : Measurable w) (hwc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z ∈ S, w (c • z) = w z)
    (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in S, w z ∂μ ≤ ∫⁻ z in S, ‖φ z‖ₑ ^ n * w z ∂μ := by sorry
