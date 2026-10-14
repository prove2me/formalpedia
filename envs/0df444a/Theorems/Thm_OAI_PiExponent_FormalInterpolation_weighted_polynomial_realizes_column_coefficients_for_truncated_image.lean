-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_polynomial_realizes_column_coefficients_for_truncated_image
-- name    : OAI.PiExponent.FormalInterpolation.weighted_polynomial_realizes_column_coefficients_for_truncated_image
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T08:08:48.117018+00:00
-- url     : https://prove2.me/theorems/133fc511-9300-48ce-84d3-1e70f8590b2c
-- title:
--   Choose a weighted polynomial with prescribed bounded coefficients
-- statement:
--   Every function on the bounded exponent set is realized by the coefficients of some weighted polynomial.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_polynomial_realizes_column_coefficients_for_truncated_image
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    ∃ Q : WeightedPolynomial w0 w H,
      ∀ c : InterpolationMatrix.Column w0 w H,
        Q.val.coeff (InterpolationMatrix.exponentVector c.1) = x c := by sorry
