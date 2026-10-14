-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_canonical_coefficients
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-13T05:14:35.456409+00:00
-- url     : https://prove2.me/theorems/00046755-50ae-46ea-9cd7-5855055d32ba
-- title:
--   The truncated packet equals the matrix applied to polynomial coefficients
-- statement:
--   The packet of a bounded polynomial equals the truncated logarithmic interpolation matrix applied to the polynomial’s monomial coefficient vector.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : WeightedPolynomial w0 w H) :
    truncatedPolynomialPacket K v0 theta w H r T P.val =
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.val.coeff (InterpolationMatrix.exponentVector c.1)) := by sorry
