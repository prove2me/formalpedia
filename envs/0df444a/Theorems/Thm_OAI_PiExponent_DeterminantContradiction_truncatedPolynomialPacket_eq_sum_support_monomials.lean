-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialPacket_eq_sum_support_monomials
-- name    : OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_sum_support_monomials
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:13:32.48399+00:00
-- url     : https://prove2.me/theorems/e88f09ea-e159-4024-922b-d701edc2a28f
-- title:
--   Expand a truncated packet over polynomial support
-- statement:
--   The packet of a polynomial is the finite sum of the packets of its supported monomials, weighted by their coefficients. This follows by expanding the polynomial and using additivity of substitution and coefficient extraction. It removes the polynomial-level expansion from the parent; it does not use the weighted bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_sum_support_monomials
    (nu : Real) (d : FixedData nu) (H : Real)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (rho : Row d H) :
    FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1 rho =
    ∑ a ∈ P.1.support,
      FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
        (MvPolynomial.monomial a 1) rho * P.1.coeff a := by sorry
