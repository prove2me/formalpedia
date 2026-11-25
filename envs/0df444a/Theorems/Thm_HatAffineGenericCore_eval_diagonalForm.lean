-- Prove2me | Theorems.Thm_HatAffineGenericCore_eval_diagonalForm
-- name    : HatAffineGenericCore.eval_diagonalForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:06.187469+00:00
-- url     : https://prove2.me/theorems/1d68a5c2-01aa-4321-bdb7-df28d2ccd703
-- title:
--   Hat Affine Generic Core: eval diagonal Form
-- statement:
--   The Hat Affine Generic Core construction uses the eval diagonal Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G3A.lean#L36-L40
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G3A.lean#L36-L40

import Mathlib
import Definitions.Def_HatAffineGenericCore_G3A
set_option autoImplicit true
open scoped BigOperators
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial

theorem HatAffineGenericCore.eval_diagonalForm {K : Type u} [CommRing K] [Fintype K] {m : Nat}
    (lambda y : Fin m → K) :
    MvPolynomial.eval y (diagonalForm lambda) =
      ∑ j, lambda j * y j ^ (Fintype.card K - 1) := by sorry
