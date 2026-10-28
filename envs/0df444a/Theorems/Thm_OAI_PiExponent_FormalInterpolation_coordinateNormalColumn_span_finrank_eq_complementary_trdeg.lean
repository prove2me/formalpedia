-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_eq_complementary_trdeg
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_eq_complementary_trdeg
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:25:01.564004+00:00
-- url     : https://prove2.me/theorems/86301481-3898-4542-b0e7-0005dee2db2c
-- title:
--   Generic coordinate Jacobian rank is complementary to transcendence degree
-- statement:
--   For a prime ideal in a polynomial ring over ℂ, the span of the coordinate derivative columns at the generic point has dimension equal to the number of coordinates minus the transcendence degree of the component’s function field.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Extension.Cotangent.Basic

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_eq_complementary_trdeg
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Submodule.span (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Set.range (OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime P))) =
      (m + 1) - (Algebra.trdeg Complex (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)).toNat := by sorry
