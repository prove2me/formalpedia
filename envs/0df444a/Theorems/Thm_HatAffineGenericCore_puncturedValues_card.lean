-- Prove2me | Theorems.Thm_HatAffineGenericCore_puncturedValues_card
-- name    : HatAffineGenericCore.puncturedValues_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:11.397069+00:00
-- url     : https://prove2.me/theorems/dbf4ff8d-6a01-467c-8aa1-d652d0d4e82b
-- title:
--   Hat Affine Generic Core: punctured Values card
-- statement:
--   The Hat Affine Generic Core construction uses the punctured Values card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L25-L28
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L25-L28

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial

theorem HatAffineGenericCore.puncturedValues_card {K : Type u} [Field K] [Fintype K]
    (g : K) : (puncturedValues g).card = Fintype.card K - 1 := by sorry
