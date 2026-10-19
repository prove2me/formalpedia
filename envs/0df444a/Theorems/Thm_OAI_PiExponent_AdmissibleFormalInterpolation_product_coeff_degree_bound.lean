-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_product_coeff_degree_bound
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.product_coeff_degree_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:54:23.481433+00:00
-- url     : https://prove2.me/theorems/4a6b5904-0ddb-41bb-a8eb-5082900db1a8
-- title:
--   Degree bound for products of low-degree-supported series
-- statement:
--   If every factor in a finite product has nonzero coefficients only at total degrees zero or one, then the product has zero coefficient at every total degree strictly greater than the number of factors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.product_coeff_degree_bound
    {σ ι R : Type*} [DecidableEq σ] [CommSemiring R]
    (s : Finset ι) (f : ι → MvPowerSeries σ R) (n : σ →₀ ℕ)
    (hs : ∀ i ∈ s, ∀ m : σ →₀ ℕ,
      MvPowerSeries.coeff m (f i) ≠ 0 → m.sum (fun _ k => k) ≤ 1)
    (h : s.card < n.sum (fun _ k => k)) :
    MvPowerSeries.coeff n (∏ i ∈ s, f i) = 0 := by sorry
