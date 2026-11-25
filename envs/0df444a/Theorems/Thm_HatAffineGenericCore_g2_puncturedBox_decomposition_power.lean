-- Prove2me | Theorems.Thm_HatAffineGenericCore_g2_puncturedBox_decomposition_power
-- name    : HatAffineGenericCore.g2_puncturedBox_decomposition_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:36.228381+00:00
-- url     : https://prove2.me/theorems/e97d219c-acee-50b6-8884-ee97c5741538
-- title:
--   Hat Affine Generic Core: g2 punctured Box decomposition power
-- statement:
--   The Hat Affine Generic Core construction uses the g2 punctured Box decomposition power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L204-L215
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L204-L215

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial

theorem HatAffineGenericCore.g2_puncturedBox_decomposition_power
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (g : Fin m → K) (P : MvPolynomial (Fin m) K)
    (hdeg : P.totalDegree ≤ Fintype.card K - 1)
    (hvanish : ∀ y : Fin m → K,
      (∀ j, y j ≠ g j) → MvPolynomial.eval y P = 0) :
    ∃ lambda : Fin m → K,
      P = ∑ j, C (lambda j) * puncturedPower g j := by sorry
