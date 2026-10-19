-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_prod_eq_one_of_support_bounds
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.coeff_prod_eq_one_of_support_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:26:41.476814+00:00
-- url     : https://prove2.me/theorems/c6dedc29-f79f-494e-96e1-9781f57fcf88
-- title:
--   Top coefficient of a product from componentwise support bounds
-- statement:
--   For a finite product of multivariate power series, if each factor is supported componentwise below its designated exponent vector and has coefficient one at that vector, then the coefficient at the sum of those vectors in the product is one. The empty finite product is included.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.coeff_prod_eq_one_of_support_bounds
    {σ R ι : Type*} [DecidableEq σ] [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (f : ι → MvPowerSeries σ R) (d : ι → (σ →₀ ℕ))
    (hsupport : ∀ i ∈ s, ∀ k : σ →₀ ℕ,
      MvPowerSeries.coeff k (f i) ≠ 0 → k ≤ d i)
    (htop : ∀ i ∈ s, MvPowerSeries.coeff (d i) (f i) = 1) :
    MvPowerSeries.coeff (∑ i ∈ s, d i) (∏ i ∈ s, f i) = 1 := by sorry
