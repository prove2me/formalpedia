-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_column_monomial_sum
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_column_monomial_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:38:09.711277+00:00
-- url     : https://prove2.me/theorems/7094abe5-8ea3-4d71-b875-fcd881adbde7
-- title:
--   The packet of the column monomial sum is the matrix image
-- statement:
--   The truncated packet of the explicit finite sum over columns equals the truncated logarithm matrix applied to the coefficient vector.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_column_monomial_sum
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    truncatedPolynomialPacket K v0 theta w H r T
        (∑ c : InterpolationMatrix.Column w0 w H,
          MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (x c)) =
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin x := by sorry
