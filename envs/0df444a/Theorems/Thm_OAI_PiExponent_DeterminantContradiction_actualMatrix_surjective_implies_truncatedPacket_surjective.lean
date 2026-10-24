-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualMatrix_surjective_implies_truncatedPacket_surjective
-- name    : OAI.PiExponent.DeterminantContradiction.actualMatrix_surjective_implies_truncatedPacket_surjective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:42:56.712021+00:00
-- url     : https://prove2.me/theorems/44821217-4ff2-47a2-870a-7becbc946867
-- title:
--   Realization of matrix preimages by weighted polynomials
-- statement:
--   At a fixed height, surjectivity of the truncated interpolation matrix implies surjectivity of the packet map on weighted polynomials by realizing a coefficient vector as a finite sum of weighted monomials.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.actualMatrix_surjective_implies_truncatedPacket_surjective
    (nu : Real) (d : FixedData nu) (H : Real)
    (hM : Function.Surjective (actualMatrix d H).mulVecLin) :
    Function.Surjective
      (fun P : WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) H
          (MatrixArithmetic.rationalCenters (finiteNumerators d)
            (finiteDenominators d))
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
          P.val) := by sorry
