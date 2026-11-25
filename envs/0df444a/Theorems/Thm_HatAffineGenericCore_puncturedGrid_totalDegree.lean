-- Prove2me | Theorems.Thm_HatAffineGenericCore_puncturedGrid_totalDegree
-- name    : HatAffineGenericCore.puncturedGrid_totalDegree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:08:04.628268+00:00
-- url     : https://prove2.me/theorems/1dc8a4e3-cba7-5568-80eb-c36951242226
-- title:
--   Hat Affine Generic Core: punctured Grid total Degree
-- statement:
--   The Hat Affine Generic Core construction uses the punctured Grid total Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L83-L86
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G2.lean#L83-L86

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial

theorem HatAffineGenericCore.puncturedGrid_totalDegree {K : Type u} [Field K] [Fintype K] {m : Nat}
    (g : Fin m → K) (j : Fin m) :
    (puncturedGrid g j).totalDegree = Fintype.card K - 1 := by sorry
