-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_polynomial_coefficient_map_surjective
-- name    : OAI.PiExponent.DeterminantContradiction.polynomial_coefficient_map_surjective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:14:08.146003+00:00
-- url     : https://prove2.me/theorems/d14bcdea-d8ce-4a57-8c20-2ff85123a591
-- title:
--   Every column vector is the coefficient vector of a weighted polynomial
-- statement:
--   Every complex-valued vector on the finite column type is represented by the monomial coefficients of some polynomial supported within the height bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.DeterminantContradiction.polynomial_coefficient_map_surjective
    (nu : Real) (d : FixedData nu) (H : Real) :
    Function.Surjective
      (fun P : WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
        fun c : Column d H =>
          P.val.coeff (InterpolationMatrix.exponentVector c.1)) := by sorry
