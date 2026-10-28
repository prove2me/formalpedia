-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fraction_field_kaehler_finrank_eq_trdeg
-- name    : OAI.PiExponent.FormalInterpolation.fraction_field_kaehler_finrank_eq_trdeg
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:34:59.766473+00:00
-- url     : https://prove2.me/theorems/0391053e-e77c-4ed2-97e3-1cb36d6557d2
-- title:
--   Differential dimension of the generic function field
-- statement:
--   The Kähler differential module of the fraction field of a prime quotient of a finite-variable complex polynomial ring has finite dimension equal to the transcendence degree of that field over ℂ.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Extension.Cotangent.Basic

theorem OAI.PiExponent.FormalInterpolation.fraction_field_kaehler_finrank_eq_trdeg
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) =
    (Algebra.trdeg Complex (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)).toNat := by sorry
