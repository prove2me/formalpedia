-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_height_add_fractionField_trdeg
-- name    : OAI.PiExponent.FormalInterpolation.height_add_fractionField_trdeg
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:55:01.171245+00:00
-- url     : https://prove2.me/theorems/0f19866c-3c19-4e03-8a0f-6684728c5005
-- title:
--   Prime height plus fraction field transcendence degree
-- statement:
--   For a prime ideal in the polynomial ring in m+1 variables over ℂ, the prime height plus the transcendence degree of the quotient's fraction field is m+1.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.height_add_fractionField_trdeg
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height.toNat + Algebra.trdeg Complex
      (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P) = m + 1 := by sorry
