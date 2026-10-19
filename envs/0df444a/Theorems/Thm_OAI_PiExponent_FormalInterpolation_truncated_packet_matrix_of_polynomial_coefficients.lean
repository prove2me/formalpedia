-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_matrix_of_polynomial_coefficients
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_of_polynomial_coefficients
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-13T08:09:06.010016+00:00
-- url     : https://prove2.me/theorems/dd066741-eae0-44fb-87a0-7a439608350e
-- title:
--   Express a truncated polynomial packet as a matrix image
-- statement:
--   For any weighted polynomial, its truncated packet equals the truncated interpolation matrix applied to its coefficients on the bounded exponent set.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_of_polynomial_coefficients
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : WeightedPolynomial w0 w H) :
    truncatedPolynomialPacket K v0 theta w H r T P.val =
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.val.coeff (InterpolationMatrix.exponentVector c.1)) := by sorry
