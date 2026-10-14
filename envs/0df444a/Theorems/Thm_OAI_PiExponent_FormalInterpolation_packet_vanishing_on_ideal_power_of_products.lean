-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_packet_vanishing_on_ideal_power_of_products
-- name    : OAI.PiExponent.FormalInterpolation.packet_vanishing_on_ideal_power_of_products
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T07:01:07.832442+00:00
-- url     : https://prove2.me/theorems/499ac0a1-1173-47b2-8791-35cd282084cd
-- title:
--   Extend product vanishing to an ideal power
-- statement:
--   If the packet at height $nR$ vanishes on every product of $n$ elements of $I$, then it vanishes on every polynomial in $I^n$, by the ideal-power span description and linearity of coefficient extraction.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.packet_vanishing_on_ideal_power_of_products
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (r : Fin m → Complex) (R : Real) (T : Fin m → Nat)
    (hR : 0 < R) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (n : Nat)
    (hProducts : ∀ f : Fin n → MvPolynomial (Fin (m + 1)) Complex,
      (∀ i, f i ∈ I) →
      truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T (∏ i, f i) = 0)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : P ∈ I ^ n) :
    truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T P = 0 := by sorry
