-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_exists_uniform_coordinate_bound
-- name    : OAI.PiExponent.WeightedDivision.exists_uniform_coordinate_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:16:28.055018+00:00
-- url     : https://prove2.me/theorems/d427369e-553b-4cef-8dbb-ae28b73f5526
-- title:
--   Uniform coordinate bound from positive weights
-- statement:
--   For a finite family of strictly positive real weights, a bound on the weighted sum gives a uniform natural-number bound on every coordinate of every finitely supported exponent vector.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.exists_uniform_coordinate_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) (B : ℝ) :
    ∃ N : ℕ, ∀ u : ι →₀ ℕ,
      (∑ i, d i * (u i : ℝ)) ≤ B → ∀ i, u i ≤ N := by sorry
