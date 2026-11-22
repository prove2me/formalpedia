-- Prove2me | Theorems.Thm_MasulloRH_log_band_weight_convolution_finite_difference_L2
-- name    : MasulloRH.log_band_weight_convolution_finite_difference_L2
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T05:26:36.842021+00:00
-- url     : https://prove2.me/theorems/5c1e04ce-8159-4a34-ad98-7662a9f4802b
-- title:
--   Weighted Riesz convolution has square-integrable translation differences
-- statement:
--   For the logarithmic strip weight $w=e^{2α|x|}(1+x²)^2$, the function $w(h*(1/w))$ is continuous, bounded, and all its finite translation differences belong to unweighted $L²$.
-- source:
--   Masullo §§9.1,9.2 and 11.2; supporting harmonic-analysis lemma for weighted spectral Riesz vectors.

import Mathlib
open MeasureTheory

theorem MasulloRH.log_band_weight_convolution_finite_difference_L2 (α : ℝ) (hα : 0 ≤ α) (h : ℝ → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h) :
    let w : ℝ → ℝ := fun x : ℝ => Real.exp (2 * α * |x|) * (1 + x^2)^2
    let b : ℝ → ℂ := fun x : ℝ => (w x : ℂ) * ∫ y : ℝ, h y / (w (x-y) : ℂ)
    Continuous b ∧ (∃ M : ℝ, ∀ x : ℝ, ‖b x‖ ≤ M) ∧ ∀ d : ℝ, MemLp (fun x => b (x+d) - b x) 2 volume := by sorry
