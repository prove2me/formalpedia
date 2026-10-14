-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_ideal_power_truncated_packet_vanishing
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_ideal_power_truncated_packet_vanishing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T05:05:25.291156+00:00
-- url     : https://prove2.me/theorems/5f6e5fee-4fa7-4615-9b32-505ef507d552
-- title:
--   Logarithmic center ideal powers vanish below the scaled row weight
-- statement:
--   If each powered logarithmic coordinate has row weight at least R, every polynomial in the nth power of the product of center ideals has zero truncated packet at height nR.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_ideal_power_truncated_packet_vanishing
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (r : Fin m → Complex) (R : Real) (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (hscale : ∀ i, R ≤ (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i)
    (n : Nat) (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : P ∈ (logarithmicCentersIdeal
      (fun j : Fin K => fun i => (j.val : Complex) * r i) T e) ^ n) :
    truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T P = 0 := by sorry
