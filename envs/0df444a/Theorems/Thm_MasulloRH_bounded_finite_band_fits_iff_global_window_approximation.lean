-- Prove2me | Theorems.Thm_MasulloRH_bounded_finite_band_fits_iff_global_window_approximation
-- name    : MasulloRH.bounded_finite_band_fits_iff_global_window_approximation
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T04:27:51.643987+00:00
-- url     : https://prove2.me/theorems/9804d941-bfde-5f33-a17c-763cb4c39292
-- title:
--   Bounded finite-band fits characterize global approximation and force error growth at an interior zero
-- statement:
--   For 0<L<U<1, arbitrary global accuracy is equivalent to fitting every finite frequency band at every tolerance with a fixed finite cap on total error. If zeta has a zero strictly between the lines, every proposed cap fails on some finite band and tolerance. A fit on that band exists, and every passing fit exceeds the cap in total squared error.
-- source:
--   For the endpoint coefficients in the Masullo fixed Gaussian approximation. https://prove2.me/theorems/be33663c-8108-4788-9dcb-d98644c8a714 The interior zero evaluation and the endpoint estimates are the published Gaussian results. https://prove2.me/submissions/cb832145-f3d4-49ca-b584-f36d57d737b6 and https://prove2.me/submissions/bb41727b-8d84-4596-befb-3f6561b45f67

import Definitions.Def_MasulloRH_FiniteMellinBands

open MeasureTheory MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest MasulloRH.RationalThetaGrid MasulloRH.VerticalThetaApproximation MasulloRH.FiniteMellinBands

theorem MasulloRH.bounded_finite_band_fits_iff_global_window_approximation (L U : ℝ) (hL : 0<L) (hLU : L<U) (hU : U<1) :
    (boundedFits L U ↔ ∀ ε : ℝ, 0<ε →
      ∃ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ), total L U a y < ε) ∧
    (∀ s : ℂ, L<s.re → s.re<U → riemannZeta s=0 → ∀ B : ℝ,
      ∃ T ε : ℝ, 0≤T ∧ 0<ε ∧
        (∃ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ), band L U T a y < ε) ∧
        ∀ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ),
          band L U T a y < ε → B<total L U a y) := by sorry
