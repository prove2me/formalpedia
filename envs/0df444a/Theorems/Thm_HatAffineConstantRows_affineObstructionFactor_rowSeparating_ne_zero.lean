-- Prove2me | Theorems.Thm_HatAffineConstantRows_affineObstructionFactor_rowSeparating_ne_zero
-- name    : HatAffineConstantRows.affineObstructionFactor_rowSeparating_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:09:03.801191+00:00
-- url     : https://prove2.me/theorems/14965350-e5f0-5923-90a8-f63820f74de7
-- title:
--   Hat Affine Constant Rows: affine Obstruction Factor row Separating ne zero
-- statement:
--   The Hat Affine Constant Rows construction uses the affine Obstruction Factor row Separating ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L136-L144
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L136-L144

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial

theorem HatAffineConstantRows.affineObstructionFactor_rowSeparating_ne_zero
    {K : Type u} [Field K] {m : Nat} {I : Type v}
    (A : I → Fin m → K) (b : I → K) (i : I) :
    affineObstructionFactor A b (rowSeparatingOffset A b) i ≠ 0 := by sorry
