-- Prove2me | Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
-- name    : HatAffineGenericCore.mem_coeffSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:06:44.504232+00:00
-- url     : https://prove2.me/theorems/46a2e649-83d2-590f-954c-12e6ff82fe74
-- title:
--   Hat Affine Generic Core: mem coeff Support
-- statement:
--   The Hat Affine Generic Core construction uses the mem coeff Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G3A.lean#L25-L29
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGenericCore/G3A.lean#L25-L29

import Mathlib
import Definitions.Def_HatAffineGenericCore_G3A
set_option autoImplicit true
open scoped BigOperators
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial

theorem HatAffineGenericCore.mem_coeffSupport {K : Type u} [Zero K] {m : Nat}
    (a : Fin m → K) (j : Fin m) :
    j ∈ coeffSupport a ↔ a j ≠ 0 := by sorry
