-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_coordinate_box_finite
-- name    : OAI.PiExponent.WeightedDivision.coordinate_box_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:16:37.613541+00:00
-- url     : https://prove2.me/theorems/2ea66f61-c049-4324-a131-3153c959b6e5
-- title:
--   Finite coordinate boxes of exponent vectors
-- statement:
--   Exponent vectors over a finite index type whose coordinates are all bounded by one natural number form a finite set.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.coordinate_box_finite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) :
    {u : ι →₀ ℕ | ∀ i, u i ≤ N}.Finite := by sorry
