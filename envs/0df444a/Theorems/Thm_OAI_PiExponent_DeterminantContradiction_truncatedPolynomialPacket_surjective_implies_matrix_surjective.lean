-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialPacket_surjective_implies_matrix_surjective
-- name    : OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_surjective_implies_matrix_surjective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:51:34.88671+00:00
-- url     : https://prove2.me/theorems/f5f52964-4c41-432b-83cb-c3c83c6d382d
-- title:
--   Truncated packet surjectivity implies matrix surjectivity
-- statement:
--   For each fixed height, surjectivity of the truncated polynomial packet map implies surjectivity of the actual interpolation matrix. Expand a weighted polynomial into its column-indexed coefficients to identify packet evaluation with matrix multiplication; represent any column vector by the finite sum of its corresponding monomials.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_surjective_implies_matrix_surjective
    (nu : Real) (d : FixedData nu) (H : Real)
    (hpacket : Function.Surjective
      (fun P : FormalInterpolation.WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
        FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) H
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1)) :
    Function.Surjective (actualMatrix d H).mulVecLin := by sorry
