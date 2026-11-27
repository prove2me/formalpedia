-- Prove2me | Theorems.Thm_MasulloRH_simultaneous_rational_theta_polynomials_on_two_finite_segments
-- name    : MasulloRH.simultaneous_rational_theta_polynomials_on_two_finite_segments
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T04:28:05.683263+00:00
-- url     : https://prove2.me/theorems/cd86d06f-d45d-4e2c-beca-f99e96b778f0
-- title:
--   Simultaneous uniform approximation of two rational exponential polynomials on finite parallel segments
-- statement:
--   Fix L<U and a finite height T. Prescribe one rational exponential polynomial on the segment L+it and another on U+it for |t|≤T. One finite exponential polynomial with rational shifts and rational real and imaginary coefficients approximates both prescribed polynomials uniformly to any positive tolerance.
-- source:
--   For the endpoint coefficients in the Masullo fixed Gaussian approximation. https://prove2.me/theorems/be33663c-8108-4788-9dcb-d98644c8a714

import Definitions.Def_MasulloRH_FiniteMellinBands

open MeasureTheory MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest MasulloRH.RationalThetaGrid MasulloRH.VerticalThetaApproximation MasulloRH.FiniteMellinBands

theorem MasulloRH.simultaneous_rational_theta_polynomials_on_two_finite_segments (L U T ε : ℝ) (hLU : L<U) (hε : 0<ε)
    {l r : ℕ} (a : Fin l → ℚ×ℚ) (x : Fin l → ℚ) (b : Fin r → ℚ×ℚ) (y : Fin r → ℚ) :
    ∃ (m : ℕ) (d : Fin m → ℚ×ℚ) (v : Fin m → ℚ), ∀ t : ℝ, |t|≤T →
      ‖poly d v (pointAt L t)-poly a x (pointAt L t)‖ < ε ∧
      ‖poly d v (pointAt U t)-poly b y (pointAt U t)‖ < ε := by sorry
