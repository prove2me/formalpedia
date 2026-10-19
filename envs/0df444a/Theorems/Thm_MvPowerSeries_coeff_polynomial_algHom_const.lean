-- Prove2me | Theorems.Thm_MvPowerSeries_coeff_polynomial_algHom_const
-- name    : MvPowerSeries.coeff_polynomial_algHom_const
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:12:30.759031+00:00
-- url     : https://prove2.me/theorems/76cb302c-2a12-4f19-8068-83328dbaf6c8
-- title:
--   Constant polynomial coefficients agree under algebra homomorphisms
-- statement:
--   For any constant polynomial and exponent, the two algebra homomorphisms have equal power-series coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

theorem MvPowerSeries.coeff_polynomial_algHom_const
    {σ τ R : Type*} [CommSemiring R]
    (F G : MvPolynomial τ R →ₐ[R] MvPowerSeries σ R)
    (j : σ) (T : ℕ) (r : R) (a : σ →₀ ℕ) (ha : a j < T) :
    MvPowerSeries.coeff a (F (MvPolynomial.C r)) =
      MvPowerSeries.coeff a (G (MvPolynomial.C r)) := by sorry
