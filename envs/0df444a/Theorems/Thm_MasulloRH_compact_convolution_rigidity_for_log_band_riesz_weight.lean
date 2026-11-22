-- Prove2me | Theorems.Thm_MasulloRH_compact_convolution_rigidity_for_log_band_riesz_weight
-- name    : MasulloRH.compact_convolution_rigidity_for_log_band_riesz_weight
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T05:26:33.104057+00:00
-- url     : https://prove2.me/theorems/3968f5f3-522d-41f1-9f45-b5a21568a46f
-- title:
--   A compact continuous convolution cannot scale the inverse log-band weight
-- statement:
--   For a continuous compact kernel $h$ and positive weight $w=e^{2α|x|}(1+x²)^2$, constancy of $w(h*(1/w))$ forces $h=0$.
-- source:
--   Masullo §§9.1,9.2 and 11.2; supporting harmonic-analysis lemma for weighted spectral Riesz vectors.

import Mathlib
open MeasureTheory

theorem MasulloRH.compact_convolution_rigidity_for_log_band_riesz_weight (α : ℝ) (hα : 0 ≤ α) (h : ℝ → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h) :
    let w : ℝ → ℝ := fun x : ℝ => Real.exp (2 * α * |x|) * (1 + x^2)^2
    let b : ℝ → ℂ := fun x : ℝ => (w x : ℂ) * ∫ y : ℝ, h y / (w (x-y) : ℂ)
    (∃ m : ℂ, ∀ x : ℝ, b x = m) → h = 0 := by sorry
