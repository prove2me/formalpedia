-- Prove2me | Theorems.Thm_MvPowerSeries_coeff_polynomial_algHom_monomial
-- name    : MvPowerSeries.coeff_polynomial_algHom_monomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:18:01.492255+00:00
-- url     : https://prove2.me/theorems/0261dd88-6bc4-4d23-96f9-10ea9fcdb518
-- title:
--   Monomial coefficients agree below a cutoff from generator agreement
-- statement:
--   If two algebra homomorphisms agree on generator coefficients below a coordinate cutoff, they agree there on the coefficients of each monomial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

theorem MvPowerSeries.coeff_polynomial_algHom_monomial
    {σ τ R : Type*} [CommSemiring R]
    (F G : MvPolynomial τ R →ₐ[R] MvPowerSeries σ R)
    (j : σ) (T : ℕ)
    (h : ∀ (i : τ) (b : σ →₀ ℕ), b j < T →
      MvPowerSeries.coeff b (F (MvPolynomial.X i)) =
        MvPowerSeries.coeff b (G (MvPolynomial.X i)))
    (s : τ →₀ ℕ) (r : R) (a : σ →₀ ℕ) (ha : a j < T) :
    MvPowerSeries.coeff a (F (MvPolynomial.monomial s r)) =
      MvPowerSeries.coeff a (G (MvPolynomial.monomial s r)) := by sorry
