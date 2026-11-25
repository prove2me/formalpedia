-- Prove2me | Theorems.Thm_HatAffineFactorAlignment_coeff_eq_zero_outside_two_of_card_le
-- name    : HatAffineFactorAlignment.coeff_eq_zero_outside_two_of_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:11:04.519349+00:00
-- url     : https://prove2.me/theorems/5fa958e7-41e9-48ba-bb81-75493fbf4f3a
-- title:
--   Hat Affine Factor Alignment: coeff eq zero outside two of card le
-- statement:
--   The Hat Affine Factor Alignment construction uses the coeff eq zero outside two of card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFactorAlignment/FactorShape.lean#L137-L153
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFactorAlignment/FactorShape.lean#L137-L153

import Definitions.Def_HatAffineGenericCore_G3A
import Definitions.Def_HatAffineFactorAlignment_FactorShape
set_option autoImplicit true
open scoped BigOperators
open HatAffineFactorAlignment
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore

theorem HatAffineFactorAlignment.coeff_eq_zero_outside_two_of_card_le
    {K : Type*} [Zero K] {m : Nat}
    (a : Fin m → K) (u v j : Fin m)
    (hcard : (coeffSupport a).card ≤ 2)
    (hau : a u ≠ 0) (hav : a v ≠ 0)
    (huv : u ≠ v) (hju : j ≠ u) (hjv : j ≠ v) :
    a j = 0 := by sorry
