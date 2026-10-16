-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_support_expansion
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_support_expansion
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-15T20:53:49.969158+00:00
-- url     : https://prove2.me/theorems/34de807b-a90f-49f5-8ec1-f2c55c98eff3
-- title:
--   Expand a truncated packet over polynomial support
-- statement:
--   For each interpolation row, the packet coefficient of a polynomial is the finite sum over its supported exponents of the monomial coefficient times the corresponding truncated interpolation matrix entry.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_support_expansion
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
    truncatedPolynomialPacket K v0 theta w H r T P rho =
      ∑ e ∈ P.support,
        P.coeff e * InterpolationMatrix.entry
          (fun i => (rho.1.val : Complex) * r i)
          (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (e 0) (fun i => e i.succ) := by sorry
