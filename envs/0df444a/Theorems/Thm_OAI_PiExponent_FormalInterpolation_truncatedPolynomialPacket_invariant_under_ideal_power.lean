-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialPacket_invariant_under_ideal_power
-- name    : OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_invariant_under_ideal_power
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:05:07.800973+00:00
-- url     : https://prove2.me/theorems/fab23a78-8f81-4a8d-a8b1-d7f71fcb5bb1
-- title:
--   Packet invariance under logarithmic center ideal powers
-- statement:
--   If two polynomials differ by the nth power of the product logarithmic center ideal, their strict truncated packets agree. Under the jet substitution at a center, its logarithmic coordinates become the ordinary coordinate variables, so the center ideal maps into the corresponding coordinate-power ideal. Its nth power therefore has no coefficient below the strict cutoff nR by hscale. At n = 0 the packet domain is empty; no distinctness assumption is needed for this vanishing argument.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_invariant_under_ideal_power
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (R : Real) (e : Fin (m + 1) → Nat) (T : Fin m → Nat)
    (r : Fin m → Complex)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i) :
    ∀ n : Nat,
      ∀ P Q : MvPolynomial (Fin (m + 1)) Complex,
        P - Q ∈
          (logarithmicCentersIdeal
            (fun j : Fin K => fun i => (j.val : Complex) * r i) T e) ^ n →
        truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T P =
          truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T Q := by sorry
