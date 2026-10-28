-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_height_add_fractionField_differential_finrank
-- name    : OAI.PiExponent.FormalInterpolation.height_add_fractionField_differential_finrank
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:49:11.73773+00:00
-- url     : https://prove2.me/theorems/43b1a969-3aff-454f-911f-eadd038065f9
-- title:
--   Fraction field differential dimension plus prime height
-- statement:
--   The differential dimension of the fraction field of the polynomial quotient, added to the height of its prime ideal, equals the ambient polynomial dimension. A proof route is the dimension formula for prime ideals in a polynomial ring over a field, together with the characteristic-zero formula identifying the dimension of the field's Kähler differentials with its transcendence degree. The zero-prime and maximal-prime cases give the respective differential dimensions m + 1 and zero.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Ideal.Height

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.height_add_fractionField_differential_finrank
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height.toNat +
      Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) = m + 1 := by sorry
