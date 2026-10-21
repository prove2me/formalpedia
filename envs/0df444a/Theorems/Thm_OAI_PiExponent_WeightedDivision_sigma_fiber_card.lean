-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_sigma_fiber_card
-- name    : OAI.PiExponent.WeightedDivision.sigma_fiber_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:39:39.262139+00:00
-- url     : https://prove2.me/theorems/39b5409a-d279-4fba-8b1d-dded0a9e3fb9
-- title:
--   Capacity of one disjoint-union fiber
-- statement:
--   The elements in the disjoint union whose first coordinate is $i$ form a fiber of cardinality $q_i$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.sigma_fiber_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (i : ι) :
    (Finset.univ.filter (fun x : Σ j, Fin (q j) => x.1 = i)).card = q i := by sorry
