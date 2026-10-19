-- Prove2me | Theorems.Thm_MvPowerSeries_coeff_polynomial_algHom_eq_of_X_eq_below
-- name    : MvPowerSeries.coeff_polynomial_algHom_eq_of_X_eq_below
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T12:06:59.953149+00:00
-- url     : https://prove2.me/theorems/d43022cd-185e-48fd-84e2-b78744c6e111
-- title:
--   Polynomial evaluation preserves coefficient agreement below a coordinate cutoff
-- statement:
--   Two polynomial algebra homomorphisms into multivariate power series agree on all polynomial coefficients below a chosen coordinate cutoff whenever they agree there on every generator. The cutoff may be zero, in which case the conclusion's exponent hypothesis is impossible.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

theorem MvPowerSeries.coeff_polynomial_algHom_eq_of_X_eq_below
    {σ τ R : Type*} [CommSemiring R]
    (F G : MvPolynomial τ R →ₐ[R] MvPowerSeries σ R)
    (j : σ) (T : ℕ)
    (h : ∀ (i : τ) (b : σ →₀ ℕ), b j < T →
      MvPowerSeries.coeff b (F (MvPolynomial.X i)) =
        MvPowerSeries.coeff b (G (MvPolynomial.X i)))
    (P : MvPolynomial τ R) (a : σ →₀ ℕ) (ha : a j < T) :
    MvPowerSeries.coeff a (F P) = MvPowerSeries.coeff a (G P) := by sorry
