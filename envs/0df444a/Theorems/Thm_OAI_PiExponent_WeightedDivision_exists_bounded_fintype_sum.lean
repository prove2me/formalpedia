-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_exists_bounded_fintype_sum
-- name    : OAI.PiExponent.WeightedDivision.exists_bounded_fintype_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:33:10.73557+00:00
-- url     : https://prove2.me/theorems/953ffef9-4151-4ed8-b540-21a07dc05683
-- title:
--   Allocate an exact total within finite capacities
-- statement:
--   For a finite family of natural-number capacities whose sum is at least s, choose a value at each index, bounded by its capacity, so that the chosen values sum to exactly s.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.exists_bounded_fintype_sum
    {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (s : ℕ)
    (hs : s ≤ ∑ i, q i) :
    ∃ k : ι → ℕ, (∀ i, k i ≤ q i) ∧ (∑ i, k i = s) := by sorry
