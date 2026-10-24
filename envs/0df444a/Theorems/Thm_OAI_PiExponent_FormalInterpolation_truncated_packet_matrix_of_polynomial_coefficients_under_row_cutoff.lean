-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_matrix_of_polynomial_coefficients_under_row_cutoff
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_of_polynomial_coefficients_under_row_cutoff
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-16T11:58:41.362977+00:00
-- url     : https://prove2.me/theorems/c86aab09-08c2-42bc-a7e9-926d88c2e6a1
-- title:
--   Express a truncated polynomial packet as a matrix image under row cutoffs
-- statement:
--   For any weighted polynomial, its packet equals the truncated interpolation matrix applied to its bounded column coefficients when each row weight is at most the corresponding truncation order times the zeroth row weight.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_of_polynomial_coefficients_under_row_cutoff
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights v0 theta w i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights v0 theta w 0)
    (P : WeightedPolynomial w0 w H) :
    truncatedPolynomialPacket K v0 theta w H r T P.val =
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.val.coeff (InterpolationMatrix.exponentVector c.1)) := by sorry
