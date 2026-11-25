-- Prove2me | Theorems.Thm_HatAffineGenericCore_g3a_support_le_two
-- name    : HatAffineGenericCore.g3a_support_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:08.319805+00:00
-- url     : https://prove2.me/theorems/d21cd3c7-9fff-46e8-8fa1-5799d2dcb311
-- title:
--   Hat Affine Generic Core: g3a support le two
-- statement:
--   The Hat Affine Generic Core construction uses the g3a support le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G3A.lean#L88-L206
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G3A.lean#L88-L206

import Mathlib
import Definitions.Def_HatAffineGenericCore_G3A
set_option autoImplicit true
open scoped BigOperators
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial

theorem HatAffineGenericCore.g3a_support_le_two
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (hq : 3 ≤ Fintype.card K)
    (a lambda : Fin m → K)
    (ha : a ≠ 0) (hlambda : lambda ≠ 0)
    (hdiv : linearForm a ∣ diagonalForm lambda) :
    (coeffSupport a).card ≤ 2 := by sorry
