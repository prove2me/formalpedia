-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialPacket_eq_column_sum
-- name    : OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_column_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:08:55.261378+00:00
-- url     : https://prove2.me/theorems/ba42ebb1-a9a8-4e78-ac2d-a0c6c694d56a
-- title:
--   Expand a truncated polynomial packet over interpolation columns
-- statement:
--   At each interpolation row, expand the truncated packet as a column-indexed sum of matrix entries weighted by the corresponding coefficients of P. This is the substantive polynomial coefficient expansion. The weighted support hypothesis ensures every supported exponent appears among the columns; columns outside the support contribute zero. The route is to expand P as a finite sum of monomials, identify the jet image of each monomial with the defining truncated-log monomial image, and apply the coefficient map.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

noncomputable section

theorem OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_column_sum
    (nu : Real) (d : FixedData nu) (H : Real)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (rho : Row d H) :
    FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1 rho =
    ∑ c : Column d H,
      actualMatrix d H rho c * P.1.coeff (InterpolationMatrix.exponentVector c.1) := by sorry
