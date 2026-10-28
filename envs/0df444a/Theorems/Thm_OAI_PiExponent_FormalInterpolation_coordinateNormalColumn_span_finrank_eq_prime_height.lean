-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_eq_prime_height
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_eq_prime_height
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T07:08:55.683965+00:00
-- url     : https://prove2.me/theorems/19afd403-f9f6-4b56-8b49-6dbd7562fe03
-- title:
--   Generic coordinate Jacobian rank equals prime height
-- statement:
--   For a prime ideal in a polynomial ring over the complex numbers, the span over the quotient’s fraction field of all coordinate derivative columns has dimension equal to the prime ideal’s height, including height zero.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_eq_prime_height
    {m : Nat} (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    (Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P)
        (Set.range (coordinateNormalColumnAtPrime P))) : ℕ∞) = P.height := by sorry
