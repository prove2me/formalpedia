-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_positive_weight_wellFounded
-- name    : OAI.PiExponent.WeightedDivision.positive_weight_wellFounded
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T07:42:34.972304+00:00
-- url     : https://prove2.me/theorems/d31f124f-e2b8-4d77-a654-a68494a0a221
-- title:
--   Positive weighted degree is well founded on finite exponent vectors
-- statement:
--   For finitely many variables with strictly positive real weights, strict decrease of weighted degree is a well-founded relation on natural exponent vectors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.positive_weight_wellFounded
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    WellFounded (fun u v : ι →₀ ℕ =>
      (∑ i, d i * (u i : ℝ)) < (∑ i, d i * (v i : ℝ))) := by sorry
