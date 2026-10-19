-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialPacket_difference_coeff_vanishes
-- name    : OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_difference_coeff_vanishes
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:11:04.159767+00:00
-- url     : https://prove2.me/theorems/defc11ac-1b83-49b0-a76b-b3cb1f025cfa
-- title:
--   Coefficient vanishing for differences in center ideal powers
-- statement:
--   For any row in the strict weighted simplex at cutoff nR, if P−Q belongs to the nth power of the product logarithmic-center ideal, then the coefficient of its jet difference at that row’s exponent vector is zero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_difference_coeff_vanishes
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (R : Real) (e : Fin (m + 1) → Nat) (T : Fin m → Nat)
    (r : Fin m → Complex)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i)
    (n : Nat) (P Q : MvPolynomial (Fin (m + 1)) Complex)
    (hPQ : P - Q ∈
      (logarithmicCentersIdeal
        (fun j : Fin K => fun i => (j.val : Complex) * r i) T e) ^ n)
    (rho : InterpolationMatrix.Row K v0 theta w ((n : Real) * R)) :
    (truncatedPolynomialJet (fun i => (rho.1.val : Complex) * r i) T (P - Q)).coeff
      (InterpolationMatrix.exponentVector rho.2.1) = 0 := by sorry
