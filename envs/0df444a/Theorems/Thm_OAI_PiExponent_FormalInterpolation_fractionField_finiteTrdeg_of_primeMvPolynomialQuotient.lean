-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fractionField_finiteTrdeg_of_primeMvPolynomialQuotient
-- name    : OAI.PiExponent.FormalInterpolation.fractionField_finiteTrdeg_of_primeMvPolynomialQuotient
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T01:04:31.755015+00:00
-- url     : https://prove2.me/theorems/1bbca8e4-ece9-4b2b-ad16-7ad3fe9c730e
-- title:
--   Finite transcendence degree of the prime quotient fraction field
-- statement:
--   The fraction field of a prime quotient of the polynomial ring in finitely many variables over `Complex` has finite transcendence degree over `Complex`. The statement includes `m = 0` and does not require the quotient to have positive dimension.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.FieldTheory.FinTrdeg

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.fractionField_finiteTrdeg_of_primeMvPolynomialQuotient
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    FinTrdeg Complex (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P) := by sorry
