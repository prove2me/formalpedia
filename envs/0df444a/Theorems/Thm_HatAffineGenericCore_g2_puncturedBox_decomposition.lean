-- Prove2me | Theorems.Thm_HatAffineGenericCore_g2_puncturedBox_decomposition
-- name    : HatAffineGenericCore.g2_puncturedBox_decomposition
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:08:21.701792+00:00
-- url     : https://prove2.me/theorems/0e176409-55ed-4f73-a5d3-6602d4316b1e
-- title:
--   Hat Affine Generic Core: g2 punctured Box decomposition
-- statement:
--   The Hat Affine Generic Core construction uses the g2 punctured Box decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L164-L202
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L164-L202

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial

theorem HatAffineGenericCore.g2_puncturedBox_decomposition
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (g : Fin m → K) (P : MvPolynomial (Fin m) K)
    (hdeg : P.totalDegree ≤ Fintype.card K - 1)
    (hvanish : ∀ y : Fin m → K,
      (∀ j, y j ≠ g j) → MvPolynomial.eval y P = 0) :
    ∃ lambda : Fin m → K,
      P = ∑ j, C (lambda j) * puncturedGrid g j := by sorry
