-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualPacket_surjective_iff_matrix_surjective
-- name    : OAI.PiExponent.DeterminantContradiction.actualPacket_surjective_iff_matrix_surjective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:07:05.019844+00:00
-- url     : https://prove2.me/theorems/943a9c50-8d1e-49dc-b613-0b9aa121c888
-- title:
--   Packet map and actual matrix have the same surjectivity
-- statement:
--   At each height, surjectivity of the truncated polynomial packet map is equivalent to surjectivity of the actual interpolation matrix. Expand supported polynomials into monomials, match each monomial packet with its matrix column, and identify the packet coordinates with matrix multiplication.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.actualPacket_surjective_iff_matrix_surjective
    (nu : Real) (d : FixedData nu) (H : Real) :
    Function.Surjective
        (fun P : WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
          truncatedPolynomialPacket d.K d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) H
            (MatrixArithmetic.rationalCenters (finiteNumerators d)
              (finiteDenominators d))
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
            P.val) ↔
      Function.Surjective (actualMatrix d H).mulVecLin := by sorry
