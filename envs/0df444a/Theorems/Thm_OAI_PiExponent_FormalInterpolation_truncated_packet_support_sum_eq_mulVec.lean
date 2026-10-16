-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_support_sum_eq_mulVec
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_support_sum_eq_mulVec
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T20:54:04.012029+00:00
-- url     : https://prove2.me/theorems/4d514a66-8ad7-41eb-9f57-2cad737b7d01
-- title:
--   Convert the supported entry sum to the canonical matrix product
-- statement:
--   Under the support-to-column condition, the finite sum of supported matrix entries equals the matrix-vector product with polynomial coefficients indexed by interpolation columns.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_support_sum_eq_mulVec
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hcols : ∀ e ∈ P.support,
      ∃ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.exponentVector c.1 = e)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
      ∑ e ∈ P.support,
        P.coeff e * InterpolationMatrix.entry
          (fun i => (rho.1.val : Complex) * r i)
          (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (e 0) (fun i => e i.succ) =
      ((InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.coeff (InterpolationMatrix.exponentVector c.1))) rho := by sorry
