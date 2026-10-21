-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_canonical_coefficients_of_positive_weights_of_support_columns
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights_of_support_columns
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:47:14.87601+00:00
-- url     : https://prove2.me/theorems/66ab541c-f394-4121-989e-71c36836f4d6
-- title:
--   Supported columns give the canonical truncated packet representation
-- statement:
--   For any polynomial whose supported exponents are represented among the interpolation columns, its truncated packet is the interpolation matrix applied to its monomial coefficient vector.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights_of_support_columns
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hcols : ∀ a ∈ P.support,
      ∃ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.exponentVector c.1 = a) :
    truncatedPolynomialPacket K v0 theta w H r T P =
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.coeff (InterpolationMatrix.exponentVector c.1)) := by sorry
