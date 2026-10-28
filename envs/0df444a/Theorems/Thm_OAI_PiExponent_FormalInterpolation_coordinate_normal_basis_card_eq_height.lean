-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_normal_basis_card_eq_height
-- name    : OAI.PiExponent.FormalInterpolation.coordinate_normal_basis_card_eq_height
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T21:22:52.349278+00:00
-- url     : https://prove2.me/theorems/ff0dcd5c-b553-40db-ab5e-53642fdbbbd6
-- title:
--   Coordinate normal rank equals prime height
-- statement:
--   A coordinate normal basis at the generic point of a prime has cardinality equal to the height of that prime.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinate_normal_basis_card_eq_height
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A) :
    A.card = P.height := by sorry
