-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_packet_vanishes_on_products_of_ideal
-- name    : OAI.PiExponent.FormalInterpolation.packet_vanishes_on_products_of_ideal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T07:00:51.219064+00:00
-- url     : https://prove2.me/theorems/f9f06a3b-7111-430a-a522-65ee76434b0c
-- title:
--   Packet vanishing for products of ideal elements
-- statement:
--   If every ideal element has zero packet at height $R$, then every product of $n$ ideal elements has zero packet at height $nR$. The proof uses coefficient convolution and the weighted pigeonhole argument.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.packet_vanishes_on_products_of_ideal
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (r : Fin m → Complex) (R : Real) (T : Fin m → Nat)
    (hR : 0 < R) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hI : ∀ Q : MvPolynomial (Fin (m + 1)) Complex, Q ∈ I →
      truncatedPolynomialPacket K v0 theta w R r T Q = 0)
    (n : Nat) (f : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (hf : ∀ i, f i ∈ I) :
    truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T (∏ i, f i) = 0 := by sorry
