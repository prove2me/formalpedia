-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialPacket_monomial_eq_actualMatrix
-- name    : OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_monomial_eq_actualMatrix
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:13:52.060123+00:00
-- url     : https://prove2.me/theorems/2de3db86-a846-49cd-be11-af72b2b621e1
-- title:
--   Identify monomial packet coefficients with matrix entries
-- statement:
--   For the monomial with exponent vector given by a column, its substituted packet coefficient equals the corresponding truncated-log matrix entry. Prove this by unfolding the packet and matrix entry, expanding `MvPolynomial.aeval` on a monomial, and matching the outer polynomial coefficient and remaining exponent coefficients. This isolates the nested coefficient calculation; no positivity or strictness assumptions are needed.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_monomial_eq_actualMatrix
    (nu : Real) (d : FixedData nu) (H : Real) (rho : Row d H)
    (c : Column d H) :
    FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1) rho =
    actualMatrix d H rho c := by sorry
