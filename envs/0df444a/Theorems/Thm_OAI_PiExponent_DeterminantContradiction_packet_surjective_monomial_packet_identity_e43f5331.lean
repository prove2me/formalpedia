-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_surjective_monomial_packet_identity_e43f5331
-- name    : OAI.PiExponent.DeterminantContradiction.packet_surjective_monomial_packet_identity_e43f5331
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:40:54.462468+00:00
-- url     : https://prove2.me/theorems/af1c139a-e755-45e7-8676-9a3b13de197d
-- title:
--   The packet of a monomial sum is its matrix coefficient sum
-- statement:
--   For the column-indexed monomial sum, each packet coordinate equals the sum of its coefficients times the corresponding actual-matrix entries.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.packet_surjective_monomial_packet_identity_e43f5331
    (nu : Real) (d : FixedData nu) (H : Real)
    (a : Column d H → Complex) :
    truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      (∑ c : Column d H,
        MvPolynomial.C (a c) *
          MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1) =
    fun rho : Row d H =>
      ∑ c : Column d H, a c * actualMatrix d H rho c := by sorry
