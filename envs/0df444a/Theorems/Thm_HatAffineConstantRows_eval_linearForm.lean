-- Prove2me | Theorems.Thm_HatAffineConstantRows_eval_linearForm
-- name    : HatAffineConstantRows.eval_linearForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:09:02.685845+00:00
-- url     : https://prove2.me/theorems/101e8c1c-32de-478b-a38a-45b68aabc568
-- title:
--   Hat Affine Constant Rows: eval linear Form
-- statement:
--   The Hat Affine Constant Rows construction uses the eval linear Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L24-L28
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L24-L28

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial

theorem HatAffineConstantRows.eval_linearForm
    {K : Type u} [CommRing K] {m : Nat}
    (a y : Fin m → K) :
    MvPolynomial.eval y (linearForm a) = ∑ j, a j * y j := by sorry
