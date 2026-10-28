-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_prime_height_add_trdeg_le_card
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_add_trdeg_le_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:38:35.60764+00:00
-- url     : https://prove2.me/theorems/fabeb982-0b05-4949-a194-fa46e38ed7ba
-- title:
--   Height plus transcendence degree is bounded by the number of coordinates
-- statement:
--   For a prime ideal in a polynomial ring in m + 1 variables over Complex, the ideal's height plus the transcendence degree of the quotient fraction field is at most m + 1.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_add_trdeg_le_card
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height + (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat ≤ m + 1 := by sorry
