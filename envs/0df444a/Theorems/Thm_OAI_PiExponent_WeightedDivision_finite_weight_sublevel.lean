-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_finite_weight_sublevel
-- name    : OAI.PiExponent.WeightedDivision.finite_weight_sublevel
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T07:53:20.548641+00:00
-- url     : https://prove2.me/theorems/97ddddca-f594-4ae6-895c-b48e83de9d62
-- title:
--   Finite sublevel sets for positive weighted degree
-- statement:
--   For finitely many coordinates with strictly positive real weights, only finitely many natural exponent vectors have weighted degree at most any fixed real bound.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.finite_weight_sublevel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) (B : ℝ) :
    {u : ι →₀ ℕ | (∑ i, d i * (u i : ℝ)) ≤ B}.Finite := by sorry
