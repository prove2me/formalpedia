-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_bound_of_floor_cost
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_bound_of_floor_cost
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:24:37.623502+00:00
-- url     : https://prove2.me/theorems/9c44ae70-f72c-49cb-87e0-db50be1ef90d
-- title:
--   Affine weight bound from a floor-cost constraint
-- statement:
--   If nonnegative weights and a nonnegative slope satisfy the per-coordinate budget, then every exponent vector whose total floor cost is below $k$ satisfies the affine weighted bound. Euclidean division separates each exponent into a budgeted multiple of $N_i$ and a remainder bounded by $N_i-1$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Real.Basic

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_bound_of_floor_cost
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (ρ : ℝ) (a N : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hρ : 0 ≤ ρ)
    (ha : ∀ i, 0 < a i) (hN : ∀ i, 0 < N i)
    (hbudget : ∀ i, (N i : ℝ) * w i ≤ (a i : ℝ) * ρ)
    (k : ℕ) (u : ι → ℕ)
    (hcost : (∑ i, a i * (u i / N i)) < k) :
    (∑ i, w i * (u i : ℝ)) ≤
      (k : ℝ) * ρ + ∑ i, w i * ((N i - 1 : ℕ) : ℝ) := by sorry
