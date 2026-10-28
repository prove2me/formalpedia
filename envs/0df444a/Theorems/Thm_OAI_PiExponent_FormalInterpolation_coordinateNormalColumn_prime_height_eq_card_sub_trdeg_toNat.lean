-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_prime_height_eq_card_sub_trdeg_toNat
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_eq_card_sub_trdeg_toNat
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:21:18.225567+00:00
-- url     : https://prove2.me/theorems/cf70641f-6055-449a-83ea-82bdef374106
-- title:
--   Prime height from affine transcendence degree
-- statement:
--   The height of a prime in this polynomial ring is the number of variables minus the transcendence degree of the fraction field of its quotient.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_eq_card_sub_trdeg_toNat
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height = ↑((m + 1) -
      (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat) := by sorry
