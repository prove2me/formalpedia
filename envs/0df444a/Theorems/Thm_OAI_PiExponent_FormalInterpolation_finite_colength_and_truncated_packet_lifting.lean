-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_colength_and_truncated_packet_lifting
-- name    : OAI.PiExponent.FormalInterpolation.finite_colength_and_truncated_packet_lifting
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:55:56.887571+00:00
-- url     : https://prove2.me/theorems/c58413e8-b99f-42cf-a530-66d68df8e898
-- title:
--   Finite colength and CRT lifting of strict truncated packets
-- statement:
--   The logarithmic center product ideal has finite colength, and every strict truncated packet lifts to a polynomial whose packet is preserved by changes in the nth ideal power. Independently prove the triangular polynomial substitution and inverse identities, identify the local ideals with coordinate-power ideals, and apply CRT at distinct centers. A nonzero coordinate of r ensures distinctness. The scale equations force positive row weights and give weight at least nR for every monomial in a local nth power, so the strict cutoff ensures vanishing. No truncation-size hypothesis is needed for this exact polynomial-jet argument. At n = 0 the row domain is empty; K = 0 also causes no obstruction.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finite_colength_and_truncated_packet_lifting
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (R : Real) (e : Fin (m + 1) → Nat) (T : Fin m → Nat)
    (r : Fin m → Complex)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i)
    (hr : ∃ i, r i ≠ 0) :
    FiniteDimensional Complex
      (MvPolynomial (Fin (m + 1)) Complex ⧸
        logarithmicCentersIdeal (fun j : Fin K => fun i => (j.val : Complex) * r i) T e) ∧
    ∀ n : Nat,
      ∀ f : InterpolationMatrix.Row K v0 theta w ((n : Real) * R) → Complex,
        ∃ P : MvPolynomial (Fin (m + 1)) Complex,
          ∀ Q : MvPolynomial (Fin (m + 1)) Complex,
            P - Q ∈
              (logarithmicCentersIdeal
                (fun j : Fin K => fun i => (j.val : Complex) * r i) T e) ^ n →
            truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T Q = f := by sorry
