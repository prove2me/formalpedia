-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fractionField_differential_finrank_eq_trdeg_toNat
-- name    : OAI.PiExponent.FormalInterpolation.fractionField_differential_finrank_eq_trdeg_toNat
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:59:14.668873+00:00
-- url     : https://prove2.me/theorems/fc841b39-be63-45b8-8747-1810bafeb48f
-- title:
--   Fraction-field differential finrank equals natural transcendence degree
-- statement:
--   For the fraction field of the prime polynomial quotient, the finrank of its Kähler differentials over `Complex` equals the natural-valued transcendence degree.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.fractionField_differential_finrank_eq_trdeg_toNat
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) =
      (Algebra.trdeg Complex
        (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)).toNat := by sorry
