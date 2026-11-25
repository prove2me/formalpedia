-- Prove2me | Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
-- name    : HatAffineGenericCore.mem_puncturedValues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:23.404281+00:00
-- url     : https://prove2.me/theorems/b1d51106-1c24-4ef1-ba77-087edf34e6a1
-- title:
--   Hat Affine Generic Core: mem punctured Values
-- statement:
--   The Hat Affine Generic Core construction uses the mem punctured Values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L20-L23
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L20-L23

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial

theorem HatAffineGenericCore.mem_puncturedValues {K : Type u} [Fintype K]
    (g x : K) : x ∈ puncturedValues g ↔ x ≠ g := by sorry
