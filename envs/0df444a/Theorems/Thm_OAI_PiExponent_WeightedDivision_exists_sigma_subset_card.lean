-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_exists_sigma_subset_card
-- name    : OAI.PiExponent.WeightedDivision.exists_sigma_subset_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:39:29.777896+00:00
-- url     : https://prove2.me/theorems/f9d811a0-d373-4ea4-bce6-2d9fbe1edac6
-- title:
--   Select a prescribed number of capacity units
-- statement:
--   If the sum of the capacities is at least $s$, the disjoint union of the corresponding finite unit sets has a subset of cardinality $s$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.exists_sigma_subset_card
    {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (s : ℕ)
    (hs : s ≤ ∑ i, q i) :
    ∃ t : Finset (Σ i, Fin (q i)), t.card = s := by sorry
