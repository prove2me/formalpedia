-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialPacket_eq_matrix_mulVec_coefficients
-- name    : OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_matrix_mulVec_coefficients
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:04:39.659997+00:00
-- url     : https://prove2.me/theorems/df29cc13-ae4f-4e14-b8d8-1cc61b96140b
-- title:
--   Truncated packet equals matrix multiplication by polynomial coefficients
-- statement:
--   For every weighted polynomial, its truncated packet equals multiplication by the actual interpolation matrix on the vector of its coefficients indexed by columns. The weighted support bound ensures every nonzero coefficient is represented among those columns.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_matrix_mulVec_coefficients
    (nu : Real) (d : FixedData nu) (H : Real)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H) :
    (actualMatrix d H).mulVecLin
      (fun c : Column d H => P.1.coeff (InterpolationMatrix.exponentVector c.1)) =
    FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1 := by sorry
