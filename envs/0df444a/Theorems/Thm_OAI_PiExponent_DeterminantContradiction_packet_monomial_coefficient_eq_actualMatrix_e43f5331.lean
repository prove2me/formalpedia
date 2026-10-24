-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_monomial_coefficient_eq_actualMatrix_e43f5331
-- name    : OAI.PiExponent.DeterminantContradiction.packet_monomial_coefficient_eq_actualMatrix_e43f5331
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:45:38.243466+00:00
-- url     : https://prove2.me/theorems/ab4506a8-68f7-48e1-a7e8-6e30ee314e0b
-- title:
--   A scalar monomial packet coefficient is its matrix entry
-- statement:
--   For each row and column, the coefficient in the truncated jet of a scalar multiple of the column's basis monomial equals that scalar times the corresponding actual-matrix entry. The proof matches the full multivariate coefficient with the matrix definition's nested polynomial and truncation coefficients.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.packet_monomial_coefficient_eq_actualMatrix_e43f5331
    (nu : Real) (d : FixedData nu) (H : Real)
    (rho : Row d H) (c : Column d H) (z : Complex) :
    (truncatedPolynomialJet
      (fun i => (rho.1.val : Complex) *
        MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      (MvPolynomial.C z *
        MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1)).coeff
      (InterpolationMatrix.exponentVector rho.2.1) =
    z * actualMatrix d H rho c := by sorry
