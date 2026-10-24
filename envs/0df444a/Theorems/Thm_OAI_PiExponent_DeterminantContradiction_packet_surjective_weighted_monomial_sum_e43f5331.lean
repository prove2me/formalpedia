-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_surjective_weighted_monomial_sum_e43f5331
-- name    : OAI.PiExponent.DeterminantContradiction.packet_surjective_weighted_monomial_sum_e43f5331
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:40:39.449262+00:00
-- url     : https://prove2.me/theorems/a7b90b1a-aaae-4624-89c1-2b135f0e2840
-- title:
--   Column-indexed monomial sums have admissible support
-- statement:
--   For coefficients indexed by the weak-cutoff columns, the finite sum of the corresponding monomials is a weighted polynomial with the same weak support bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.packet_surjective_weighted_monomial_sum_e43f5331
    (nu : Real) (d : FixedData nu) (H : Real)
    (a : Column d H → Complex) :
    ∃ P : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      P.1 =
        ∑ c : Column d H,
          MvPolynomial.C (a c) *
            MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1 := by sorry
