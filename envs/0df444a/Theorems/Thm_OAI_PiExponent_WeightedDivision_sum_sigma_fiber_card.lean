-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_sum_sigma_fiber_card
-- name    : OAI.PiExponent.WeightedDivision.sum_sigma_fiber_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:39:54.06913+00:00
-- url     : https://prove2.me/theorems/7444107e-4df5-4d92-a0a6-4beeefdfa3ff
-- title:
--   Fiber counts partition a finite subset
-- statement:
--   Summing the fiber cardinalities of any finite subset of the disjoint union recovers the subset's cardinality.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.sum_sigma_fiber_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ι → ℕ}
    (t : Finset (Σ i, Fin (q i))) :
    (∑ i, (t.filter fun x : Σ j, Fin (q j) => x.1 = i).card) = t.card := by sorry
