-- Prove2me | Theorems.Thm_MvPowerSeries_coeff_polynomial_algHom_add
-- name    : MvPowerSeries.coeff_polynomial_algHom_add
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:12:39.411977+00:00
-- url     : https://prove2.me/theorems/cacf2042-6558-4ee9-9508-05cbc4da451d
-- title:
--   Coefficient agreement below a cutoff is preserved by polynomial addition
-- statement:
--   If the images of two polynomials have equal coefficients below the cutoff, coefficient agreement below the cutoff also holds for their sum.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

theorem MvPowerSeries.coeff_polynomial_algHom_add
    {σ τ R : Type*} [CommSemiring R]
    (F G : MvPolynomial τ R →ₐ[R] MvPowerSeries σ R)
    (j : σ) (T : ℕ)
    (p q : MvPolynomial τ R) (a : σ →₀ ℕ) (ha : a j < T)
    (hp : ∀ b : σ →₀ ℕ, b j < T →
      MvPowerSeries.coeff b (F p) = MvPowerSeries.coeff b (G p))
    (hq : ∀ b : σ →₀ ℕ, b j < T →
      MvPowerSeries.coeff b (F q) = MvPowerSeries.coeff b (G q)) :
    MvPowerSeries.coeff a (F (p + q)) = MvPowerSeries.coeff a (G (p + q)) := by sorry
