-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_matrix_of_polynomial_coefficients_of_pos
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_of_polynomial_coefficients_of_pos
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:16:59.124622+00:00
-- url     : https://prove2.me/theorems/aff273f6-6a2e-4a1e-8179-48c0aba2422e
-- title:
--   Truncated packet equals matrix mulVec for positive-weight weighted polynomials
-- statement:
--   When column weights and the height are strictly positive, a weighted polynomial's truncated packet equals the truncated-log matrix applied to its column coefficients. Positivity places every support exponent in the real weighted simplex, so the support sum of jet coefficients reindexes to the matrix column sum.
-- source:
--   Reindexing of truncated_polynomial_jet_support_expansion via weighted_coordinates_mem_realWeightedSimplex and truncated_packet_support_sum_eq_column_sum under positive weights.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_of_polynomial_coefficients_of_pos
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (hH : 0 < H)
    (P : WeightedPolynomial w0 w H) :
    truncatedPolynomialPacket K v0 theta w H r T P.val =
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.val.coeff (InterpolationMatrix.exponentVector c.1)) := by sorry
