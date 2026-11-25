-- Prove2me | Theorems.Thm_HatAffineConstantRows_affineObstructionFactor_rowSeparating_of_ne_zero
-- name    : HatAffineConstantRows.affineObstructionFactor_rowSeparating_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:09:19.862796+00:00
-- url     : https://prove2.me/theorems/3e7e8796-1812-43ab-8bb2-273e6ee9a934
-- title:
--   Hat Affine Constant Rows: affine Obstruction Factor row Separating of ne zero
-- statement:
--   The Hat Affine Constant Rows construction uses the affine Obstruction Factor row Separating of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L129-L134
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L129-L134

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial

theorem HatAffineConstantRows.affineObstructionFactor_rowSeparating_of_ne_zero
    {K : Type u} [Field K] {m : Nat} {I : Type v}
    (A : I → Fin m → K) (b : I → K) (i : I) (hi : A i ≠ 0) :
    affineObstructionFactor A b (rowSeparatingOffset A b) i = linearForm (A i) := by sorry
