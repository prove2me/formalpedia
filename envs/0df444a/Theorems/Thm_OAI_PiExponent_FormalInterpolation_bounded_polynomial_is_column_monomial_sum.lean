-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_polynomial_is_column_monomial_sum
-- name    : OAI.PiExponent.FormalInterpolation.bounded_polynomial_is_column_monomial_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:37:55.44313+00:00
-- url     : https://prove2.me/theorems/41ed052c-bad6-4fb8-be67-6f63cd869bdd
-- title:
--   The column monomial sum is a bounded weighted polynomial
-- statement:
--   For any coefficient vector on the admissible columns, its finite sum of corresponding monomials is a weighted polynomial satisfying the same support bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.bounded_polynomial_is_column_monomial_sum
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    ∃ Q : WeightedPolynomial w0 w H,
      Q.val = ∑ c : InterpolationMatrix.Column w0 w H,
        MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (x c) := by sorry
