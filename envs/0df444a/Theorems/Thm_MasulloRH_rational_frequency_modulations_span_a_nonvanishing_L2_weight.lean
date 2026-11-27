-- Prove2me | Theorems.Thm_MasulloRH_rational_frequency_modulations_span_a_nonvanishing_L2_weight
-- name    : MasulloRH.rational_frequency_modulations_span_a_nonvanishing_L2_weight
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T04:02:35.803818+00:00
-- url     : https://prove2.me/theorems/5d94add4-acdf-49bd-801e-2e3c30293afe
-- title:
--   Rational frequencies and rational complex coefficients are dense for a nonvanishing L² multiplier
-- statement:
--   For any square-integrable complex H nonzero almost everywhere on the real frequency axis, any square-integrable target A, any real slope c, and any positive tolerance, a finite sum of H(t) exp((c+it)y) at rational y with complex rational coefficients approximates A in squared L² error below that tolerance.
-- source:
--   For the fixed Gaussian approximation on the expanding windows in the Masullo specialization. https://prove2.me/theorems/a73312ae-c4b7-4b9d-8ac1-61f52cc8523d

import Definitions.Def_MasulloRH_VerticalThetaApproximation

open MeasureTheory MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest MasulloRH.RationalThetaGrid MasulloRH.VerticalThetaApproximation

theorem MasulloRH.rational_frequency_modulations_span_a_nonvanishing_L2_weight (c : ℝ) (A H : ℝ → ℂ) (hA : MemLp A 2) (hH : MemLp H 2)
    (hn : ∀ᵐ t : ℝ, H t ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      (∫ t : ℝ, ‖A t - H t * ∑ i, asComplex (a i) * Complex.exp (pointAt c t * (y i : ℝ))‖^2) < ε := by sorry
