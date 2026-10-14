-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_packet_vanishes_on_products_with_individual_heights
-- name    : OAI.PiExponent.FormalInterpolation.packet_vanishes_on_products_with_individual_heights
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T07:29:02.03058+00:00
-- url     : https://prove2.me/theorems/b7ac217e-9257-490a-a685-fdcb824acdf3
-- title:
--   Packet vanishing for products with individual heights
-- statement:
--   If each polynomial factor has a vanishing packet at its own positive height, then the packet of their product vanishes at the sum of those heights. This isolates the coefficient-convolution and weighted pigeonhole step independently of ideal membership.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.packet_vanishes_on_products_with_individual_heights
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (r : Fin m → Complex) {n : Nat} (R : Fin n → Real) (T : Fin m → Nat)
    (hR : ∀ i, 0 < R i) (hw : ∀ i, 0 < w i)
    (f : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (hf : ∀ i,
      truncatedPolynomialPacket K v0 theta w (R i) r T (f i) = 0) :
    truncatedPolynomialPacket K v0 theta w (∑ i, R i) r T (∏ i, f i) = 0 := by sorry
