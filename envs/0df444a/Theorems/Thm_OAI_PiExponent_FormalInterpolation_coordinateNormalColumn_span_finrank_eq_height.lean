-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_eq_height
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_eq_height
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T23:54:19.514691+00:00
-- url     : https://prove2.me/theorems/0c308b33-493f-42a2-8a0a-7765c4e3a1da
-- title:
--   Generic coordinate derivative rank equals prime height
-- statement:
--   For a prime ideal in the polynomial ring over ℂ, the span over the fraction field of the prime quotient of all coordinate derivative columns has dimension equal to the prime’s height. For the zero prime both sides are zero; in general this is the generic conormal rank computation.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_eq_height
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P)
        (Set.range (coordinateNormalColumnAtPrime P))) = P.height := by sorry
