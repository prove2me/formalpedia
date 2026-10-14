-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_packet_vanishing_on_ideal_implies_vanishing_on_powers
-- name    : OAI.PiExponent.FormalInterpolation.packet_vanishing_on_ideal_implies_vanishing_on_powers
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T06:46:16.329133+00:00
-- url     : https://prove2.me/theorems/4a1893c3-6275-42a5-bd98-3d63fc91c9c0
-- title:
--   Packet vanishing extends to powers of an ideal
-- statement:
--   If every element of an ideal has zero packet at height R, every element of its nth power has zero packet at height nR.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.packet_vanishing_on_ideal_implies_vanishing_on_powers
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (r : Fin m → Complex) (R : Real) (T : Fin m → Nat)
    (hR : 0 < R) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hI : ∀ Q : MvPolynomial (Fin (m + 1)) Complex, Q ∈ I →
      truncatedPolynomialPacket K v0 theta w R r T Q = 0)
    (n : Nat) (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : P ∈ I ^ n) :
    truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T P = 0 := by sorry
