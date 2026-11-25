-- Prove2me | Theorems.Thm_HatAffineConstantRows_affineObstructionFactor_rowSeparating_of_zero
-- name    : HatAffineConstantRows.affineObstructionFactor_rowSeparating_of_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:09:27.314797+00:00
-- url     : https://prove2.me/theorems/0f76cd4e-f5fe-44b5-b02d-4771fa91a10d
-- title:
--   Hat Affine Constant Rows: affine Obstruction Factor row Separating of zero
-- statement:
--   The Hat Affine Constant Rows construction uses the affine Obstruction Factor row Separating of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L122-L127
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L122-L127

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial

theorem HatAffineConstantRows.affineObstructionFactor_rowSeparating_of_zero
    {K : Type u} [Field K] {m : Nat} {I : Type v}
    (A : I → Fin m → K) (b : I → K) (i : I) (hi : A i = 0) :
    affineObstructionFactor A b (rowSeparatingOffset A b) i = C (-1) := by sorry
