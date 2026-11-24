-- Prove2me | Theorems.Thm_GlobalTheory_measure_univ_le_two_mul_sublevel_of_drift
-- name    : GlobalTheory.measure_univ_le_two_mul_sublevel_of_drift
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:38.709385+00:00
-- url     : https://prove2.me/theorems/4cdfc3dd-d31a-4503-9e45-d1d9ceaf4ed2
-- title:
--   Global Theory: measure univ le two mul sublevel of drift
-- statement:
--   The Global Theory construction uses the measure univ le two mul sublevel of drift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasureUnivLeTwoMulSublevelOfDrift.lean#L8-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasureUnivLeTwoMulSublevelOfDrift.lean#L8-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasureUnivLeTwoMulSublevelOfDrift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory

theorem GlobalTheory.measure_univ_le_two_mul_sublevel_of_drift :
    (∀ (Y σ : Type) [MeasurableSpace Y] [Fintype σ] [Nonempty σ] (μ : Measure Y)
      (R : Y → Y → Prop) (t : σ → Y → Y) (f : Y → ℝ) (c b : ℝ), (∀ s, Measurable (t s)) →
      (∀ s y y', R y y' → R (t s y) (t s y')) →
      (∀ φ : Y → ℝ≥0∞, Measurable φ → (∀ y y', R y y' → φ y = φ y') →
        ∀ s, ∫⁻ y, φ (t s y) ∂μ = ∫⁻ y, φ y ∂μ) →
      Measurable f → (∀ y, 0 ≤ f y) → (∀ y y', R y y' → f y = f y') → 0 ≤ c → c < 1 → 0 ≤ b →
      (∀ y, ∑ s, f (t s y) ≤ Fintype.card σ * (c * f y + b)) →
      ∃ M : ℝ, μ Set.univ ≤ 2 * μ {y | f y ≤ M}) := by sorry
