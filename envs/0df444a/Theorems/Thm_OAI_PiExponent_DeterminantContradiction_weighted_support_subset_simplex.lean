-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_support_subset_simplex
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_support_subset_simplex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:31:56.966325+00:00
-- url     : https://prove2.me/theorems/0cd27f03-9c74-4231-a875-9bfb4811a46a
-- title:
--   A weighted polynomial support lies in its inclusive simplex
-- statement:
--   Every function-index encoding of an exponent in the weighted polynomial's support belongs to the finite inclusive simplex defined by the same weight bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.DeterminantContradiction.weighted_support_subset_simplex
    (nu : Real) (d : FixedData nu) (H : Real)
    (P : WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H) :
    P.1.support.map Finsupp.equivFunOnFinite.toEmbedding ⊆
      realWeightedSimplex
        (InterpolationMatrix.columnWeights d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d))) H := by sorry
