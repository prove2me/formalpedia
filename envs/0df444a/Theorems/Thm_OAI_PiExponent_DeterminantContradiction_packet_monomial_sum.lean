-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_monomial_sum
-- name    : OAI.PiExponent.DeterminantContradiction.packet_monomial_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:19:42.254266+00:00
-- url     : https://prove2.me/theorems/1dbae39d-3814-457b-9b19-6faa89989fe6
-- title:
--   Packets of monomial sums equal matrix coefficient sums
-- statement:
--   For coefficients indexed by the weak weighted simplex, the truncated polynomial packet of their monomial sum is the row-wise sum of those coefficients times the corresponding actual matrix entries.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.packet_monomial_sum
    (nu : Real) (d : FixedData nu) (H : Real)
    (a : Column d H → Complex) :
    truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      (∑ c : Column d H,
        MvPolynomial.C (a c) *
          MvPolynomial.monomial
            (InterpolationMatrix.exponentVector c.1) 1) =
      fun rho : Row d H =>
        ∑ c : Column d H, a c * actualMatrix d H rho c := by sorry
