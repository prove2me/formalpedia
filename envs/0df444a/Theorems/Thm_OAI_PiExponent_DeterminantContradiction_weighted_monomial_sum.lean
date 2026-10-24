-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_monomial_sum
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_monomial_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:19:27.970362+00:00
-- url     : https://prove2.me/theorems/ab189c4e-734d-42d4-8c54-221bba52f028
-- title:
--   Weak-cutoff coefficients form an admissible polynomial
-- statement:
--   For any coefficients indexed by the weak weighted simplex columns, the corresponding finite sum of monomials is a weighted polynomial with the same weak support cutoff.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weighted_monomial_sum
    (nu : Real) (d : FixedData nu) (H : Real)
    (a : Column d H → Complex) :
    ∃ P : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      P.1 =
        ∑ c : Column d H,
          MvPolynomial.C (a c) *
            MvPolynomial.monomial
              (InterpolationMatrix.exponentVector c.1) 1 := by sorry
