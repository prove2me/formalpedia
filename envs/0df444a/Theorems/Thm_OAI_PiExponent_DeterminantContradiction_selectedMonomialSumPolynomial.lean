-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_selectedMonomialSumPolynomial
-- name    : OAI.PiExponent.DeterminantContradiction.selectedMonomialSumPolynomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:11:59.326024+00:00
-- url     : https://prove2.me/theorems/d906c52d-1ec6-445d-8e90-ba94b7c9f755
-- title:
--   Selected column monomials form a weighted polynomial
-- statement:
--   The finite sum of selected column monomials with coefficients x has weighted support bounded by H.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.selectedMonomialSumPolynomial
    (nu : Real) (d : FixedData nu) (H : Real)
    (selection : Row d H → Column d H)
    (x : Row d H → Complex) :
    ∃ P : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      P.1 = ∑ sigma : Row d H,
        MvPolynomial.C (x sigma) *
          MvPolynomial.monomial
            (InterpolationMatrix.exponentVector (selection sigma).1) 1 := by
  sorry
