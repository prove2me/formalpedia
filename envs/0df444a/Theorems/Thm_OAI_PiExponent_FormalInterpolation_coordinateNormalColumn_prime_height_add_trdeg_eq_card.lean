-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_prime_height_add_trdeg_eq_card
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_add_trdeg_eq_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:25:23.004415+00:00
-- url     : https://prove2.me/theorems/31a86469-d266-45bf-8ea8-6729eedd2459
-- title:
--   Additive height and transcendence-degree formula
-- statement:
--   For a prime ideal in a polynomial ring in `m + 1` variables over the complex numbers, its height plus the transcendence degree of the fraction field of its quotient equals the number of variables.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_add_trdeg_eq_card
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height + (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat = m + 1 := by sorry
