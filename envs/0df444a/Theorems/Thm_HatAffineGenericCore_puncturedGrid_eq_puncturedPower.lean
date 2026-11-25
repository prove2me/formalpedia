-- Prove2me | Theorems.Thm_HatAffineGenericCore_puncturedGrid_eq_puncturedPower
-- name    : HatAffineGenericCore.puncturedGrid_eq_puncturedPower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:08:29.073195+00:00
-- url     : https://prove2.me/theorems/8533f988-e904-48eb-b6f4-0a986bec1924
-- title:
--   Hat Affine Generic Core: punctured Grid eq punctured Power
-- statement:
--   The Hat Affine Generic Core construction uses the punctured Grid eq punctured Power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L156-L162
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L156-L162

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial

theorem HatAffineGenericCore.puncturedGrid_eq_puncturedPower
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (g : Fin m → K) (j : Fin m) :
    puncturedGrid g j = puncturedPower g j := by sorry
