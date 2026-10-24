-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualMatrix_mulVec_coefficients_eq_column_sum
-- name    : OAI.PiExponent.DeterminantContradiction.actualMatrix_mulVec_coefficients_eq_column_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:09:20.114454+00:00
-- url     : https://prove2.me/theorems/5b16b543-a364-44fd-990a-5f94a2875476
-- title:
--   Evaluate the interpolation matrix-vector product by columns
-- statement:
--   Express the row coordinate of the actual matrix applied to the polynomial coefficient vector as its finite sum over columns. This is the standard matrix-vector coordinate formula and is independent of polynomial jets; prove it by unfolding `mulVecLin` and the finite matrix-vector sum.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

noncomputable section

theorem OAI.PiExponent.DeterminantContradiction.actualMatrix_mulVec_coefficients_eq_column_sum
    (nu : Real) (d : FixedData nu) (H : Real)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (rho : Row d H) :
    (actualMatrix d H).mulVecLin
      (fun c : Column d H => P.1.coeff (InterpolationMatrix.exponentVector c.1)) rho =
    ∑ c : Column d H,
      actualMatrix d H rho c * P.1.coeff (InterpolationMatrix.exponentVector c.1) := by sorry
