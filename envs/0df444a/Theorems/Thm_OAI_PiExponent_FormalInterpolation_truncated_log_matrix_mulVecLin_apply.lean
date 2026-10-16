-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_log_matrix_mulVecLin_apply
-- name    : OAI.PiExponent.FormalInterpolation.truncated_log_matrix_mulVecLin_apply
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:56:03.847627+00:00
-- url     : https://prove2.me/theorems/36117248-5eed-4e46-a5de-0661f19b54fa
-- title:
--   Expand the truncated logarithm matrix-vector application
-- statement:
--   Evaluate the matrix-vector linear map at a row as the finite sum of its matrix entries multiplied by the supplied column coefficients.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_log_matrix_mulVecLin_apply
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
      ((InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.coeff (InterpolationMatrix.exponentVector c.1))) rho =
      ∑ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.entry
          r (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (c.1 0) (fun i => c.1 i.succ) *
        P.coeff (InterpolationMatrix.exponentVector c.1) := by sorry
