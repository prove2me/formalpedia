-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalBasis_card_eq_height
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalBasis_card_eq_height
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:57:39.840279+00:00
-- url     : https://prove2.me/theorems/d8bf2c63-7227-447f-b284-82576c11d8c0
-- title:
--   Generic coordinate normal rank equals prime height
-- statement:
--   For a prime ideal in this polynomial ring, a basis selected from the coordinate derivative columns has cardinality equal to the prime's height. The statement also covers height zero, where the derivative span and basis are empty.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalBasis_card_eq_height
    {m : Nat} (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A) :
    (A.card : ℕ∞) = P.height := by
  sorry
