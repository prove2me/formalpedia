-- Prove2me | Theorems.Thm_HatAffineGenericCore_eval_linearForm
-- name    : HatAffineGenericCore.eval_linearForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:06:49.693217+00:00
-- url     : https://prove2.me/theorems/886a0bcf-cd4e-55db-9611-147519fb209a
-- title:
--   Hat Affine Generic Core: eval linear Form
-- statement:
--   The Hat Affine Generic Core construction uses the eval linear Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G3A.lean#L31-L34
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G3A.lean#L31-L34

import Mathlib
import Definitions.Def_HatAffineGenericCore_G3A
set_option autoImplicit true
open scoped BigOperators
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial

theorem HatAffineGenericCore.eval_linearForm {K : Type u} [CommRing K] {m : Nat}
    (a y : Fin m → K) :
    MvPolynomial.eval y (linearForm a) = ∑ j, a j * y j := by sorry
