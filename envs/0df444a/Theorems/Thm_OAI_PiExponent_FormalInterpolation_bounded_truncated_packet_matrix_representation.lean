-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_truncated_packet_matrix_representation
-- name    : OAI.PiExponent.FormalInterpolation.bounded_truncated_packet_matrix_representation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T05:05:47.96048+00:00
-- url     : https://prove2.me/theorems/0fa03269-11f2-430c-8554-9e5c4e512e95
-- title:
--   Bounded polynomial packets are represented by the truncated interpolation matrix
-- statement:
--   The truncated polynomial packet of a polynomial supported within column weight H belongs to the image of the truncated logarithmic interpolation matrix.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.bounded_truncated_packet_matrix_representation
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (P : WeightedPolynomial w0 w H) :
    ∃ x : InterpolationMatrix.Column w0 w H → Complex,
      truncatedPolynomialPacket K v0 theta w H r T P.val =
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin x := by sorry
