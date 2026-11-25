-- Prove2me | Theorems.Thm_HatAffineConstantRows_linearForm_ne_zero_iff
-- name    : HatAffineConstantRows.linearForm_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:09:05.663803+00:00
-- url     : https://prove2.me/theorems/c1213ccc-fb27-41df-adb5-cc1ada89dd3d
-- title:
--   Hat Affine Constant Rows: linear Form ne zero iff
-- statement:
--   The Hat Affine Constant Rows construction uses the linear Form ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L43-L46
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L43-L46

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial

theorem HatAffineConstantRows.linearForm_ne_zero_iff
    {K : Type u} [Field K] {m : Nat} (a : Fin m → K) :
    linearForm a ≠ 0 ↔ a ≠ 0 := by sorry
