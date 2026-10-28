-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumnAtPrime_finrank_eq_height
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime_finrank_eq_height
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:48:48.710879+00:00
-- url     : https://prove2.me/theorems/d4f5da40-2b5b-4861-a0b1-1035dd2396f9
-- title:
--   Generic coordinate Jacobian rank equals prime height
-- statement:
--   For a prime ideal in a polynomial ring over Complex, the span of the generic coordinate derivative columns has dimension equal to the height of the prime ideal. This is the characteristic-zero generic Jacobian criterion, applied over the fraction field of the quotient. It handles the zero ideal with rank zero and a maximal ideal with full ambient rank.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Ideal.Height

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime_finrank_eq_height
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Submodule.span (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Set.range (OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime P))) =
      P.height.toNat := by sorry
