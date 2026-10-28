-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_add_trdeg_toNat
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_add_trdeg_toNat
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:20:58.073552+00:00
-- url     : https://prove2.me/theorems/43823444-e734-4445-bfb0-6f5311cc54b1
-- title:
--   Coordinate derivative rank plus transcendence degree
-- statement:
--   The rank of the span of all coordinate derivative columns, plus the transcendence degree of the prime quotient’s fraction field, equals the number of coordinates.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Extension.Cotangent.Basic

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_add_trdeg_toNat
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P)
        (Set.range (coordinateNormalColumnAtPrime P))) +
      (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat = m + 1 := by sorry
