-- Prove2me | Theorems.Thm_HatAffineGenericCore_puncturedSet_card
-- name    : HatAffineGenericCore.puncturedSet_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:18.262099+00:00
-- url     : https://prove2.me/theorems/464747cc-9e50-45a0-8377-36ec36c69d87
-- title:
--   Hat Affine Generic Core: punctured Set card
-- statement:
--   The Hat Affine Generic Core construction uses the punctured Set card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L64-L68
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L64-L68

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial

theorem HatAffineGenericCore.puncturedSet_card {K : Type u} [Field K] [Fintype K] {m : Nat}
    (g : Fin m → K) (j : Fin m) :
    (puncturedSet g j).card = Fintype.card K - 1 := by sorry
