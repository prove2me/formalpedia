-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_support_sum_eq_column_sum
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_support_sum_eq_column_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:55:48.95781+00:00
-- url     : https://prove2.me/theorems/691d015a-adaf-43fa-a7b5-4983ec788a6f
-- title:
--   Reindex the supported entry sum by interpolation columns
-- statement:
--   Reindex the sum over polynomial support as a sum over interpolation columns. The support coverage hypothesis provides columns for supported exponents; columns outside the support have zero coefficient, and the exponent encoding identifies the corresponding terms.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_support_sum_eq_column_sum
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hcols : ∀ e ∈ P.support,
      ∃ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.exponentVector c.1 = e)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
      ∑ e ∈ P.support,
        P.coeff e * InterpolationMatrix.entry
          r (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (e 0) (fun i => e i.succ) =
      ∑ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.entry
          r (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (c.1 0) (fun i => c.1 i.succ) *
        P.coeff (InterpolationMatrix.exponentVector c.1) := by sorry
