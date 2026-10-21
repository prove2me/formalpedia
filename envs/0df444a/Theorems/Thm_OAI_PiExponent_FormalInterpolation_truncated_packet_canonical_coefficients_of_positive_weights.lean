-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_canonical_coefficients_of_positive_weights
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:41:58.258423+00:00
-- url     : https://prove2.me/theorems/40a2bee0-3427-4db2-a58b-9c37b102c522
-- title:
--   Positive weights give the canonical truncated packet representation
-- statement:
--   For a polynomial whose support is bounded by positive column weights, its truncated packet equals the truncated logarithmic interpolation matrix applied to its monomial coefficient vector.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (P : WeightedPolynomial w0 w H) :
    truncatedPolynomialPacket K v0 theta w H r T P.val =
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.val.coeff (InterpolationMatrix.exponentVector c.1)) := by sorry
