-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_matrix_image_representative
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_image_representative
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T05:31:20.765223+00:00
-- url     : https://prove2.me/theorems/0db5f6ff-536f-4dcd-8bfe-2cba56a1b44e
-- title:
--   Every truncated matrix image has a bounded polynomial packet representative
-- statement:
--   For any coefficient vector indexed by the admissible weighted columns, there is a weighted polynomial whose truncated packet equals the image of that vector under the truncated logarithm matrix.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_image_representative
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    ∃ Q : WeightedPolynomial w0 w H,
      truncatedPolynomialPacket K v0 theta w H r T Q.val =
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin x := by sorry
