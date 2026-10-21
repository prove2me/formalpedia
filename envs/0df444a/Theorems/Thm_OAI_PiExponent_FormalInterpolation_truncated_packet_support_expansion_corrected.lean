-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_support_expansion_corrected
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_support_expansion_corrected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:51:50.097469+00:00
-- url     : https://prove2.me/theorems/d404957a-4753-4389-b315-cbb2f2caad31
-- title:
--   Expand the truncated packet with the matrix’s row scaling
-- statement:
--   For each row, expand the packet as the finite sum over polynomial support, using the original center vector `r` as the argument to `entry`; `entry` itself applies the row index.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_support_expansion_corrected
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
    truncatedPolynomialPacket K v0 theta w H r T P rho =
      ∑ e ∈ P.support,
        P.coeff e * InterpolationMatrix.entry
          r (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (e 0) (fun i => e i.succ) := by sorry
