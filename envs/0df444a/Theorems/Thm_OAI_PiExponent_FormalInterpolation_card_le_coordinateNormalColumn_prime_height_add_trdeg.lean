-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_card_le_coordinateNormalColumn_prime_height_add_trdeg
-- name    : OAI.PiExponent.FormalInterpolation.card_le_coordinateNormalColumn_prime_height_add_trdeg
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:38:53.748573+00:00
-- url     : https://prove2.me/theorems/bac71d4b-887d-4d31-b11e-596fda71b095
-- title:
--   The number of coordinates is bounded by height plus transcendence degree
-- statement:
--   For a prime ideal in a polynomial ring in m + 1 variables over Complex, m + 1 is at most the ideal's height plus the transcendence degree of the quotient fraction field.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.card_le_coordinateNormalColumn_prime_height_add_trdeg
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    m + 1 ≤ P.height + (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat := by sorry
