-- Prove2me | Theorems.Thm_LogLogJam_Supplement_phase_location_from_samples
-- name    : LogLogJam.Supplement.phase_location_from_samples
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T19:20:43.772001+00:00
-- url     : https://prove2.me/theorems/69224358-8a35-4edf-8d5f-2b7caee05138
-- title:
--   Uniform circular location estimation from squeezed phase samples
-- statement:
--   For independent real observations whose first half have the displayed squeezed-phase density, a measurable estimator of the half-angle attains sine error at most η in units of sinh(2r) with failure probability δ from O(log(2/δ)/η²) observations. The estimator uses only phase samples and is independent of the two unknown parameters.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3

import Mathlib
open MeasureTheory
open scoped ENNReal

namespace LogLogJam.Supplement

theorem phase_location_from_samples :
    ∃ C > (0 : ℝ), ∀ η δ : ℝ, 0 < η → η ≤ 1 / 4 → 0 < δ → δ < 1 →
    ∀ m : ℕ, C * Real.log (2 / δ) / η^2 ≤ m →
    ∃ angle : (Fin m → ℝ) → ℝ, Measurable angle ∧
      (∀ x y, (∀ i : Fin m, i.val < m / 2 → x i = y i) → angle x = angle y) ∧
      ∀ (r θ : ℝ), 0 ≤ r → ∀ μ : Fin m → Measure ℝ,
        (∀ i, IsProbabilityMeasure (μ i)) →
        (∀ (i : Fin m), i.val < m / 2 → ∀ B : Set ℝ, MeasurableSet B →
          let b := fun n : ℕ => Real.sqrt (Nat.centralBinom n) / (2:ℝ)^n
          let z := (Real.tanh r : ℂ) * Complex.exp ((2*θ:ℝ)*Complex.I)
          μ i B = ENNReal.ofReal ((∫ x in B ∩ Set.Ico 0 (2*Real.pi),
            ‖∑' n, (((b n / Real.sqrt (Real.cosh r) : ℝ) : ℂ) * z^n) *
              Complex.exp (-(n:ℂ)*(x:ℂ)*Complex.I)‖^2) / (2 * Real.pi))) →
        Measure.pi μ {x | η < Real.sinh (2*r) * |Real.sin (θ - angle x)|} ≤ ENNReal.ofReal δ := by sorry

end LogLogJam.Supplement
