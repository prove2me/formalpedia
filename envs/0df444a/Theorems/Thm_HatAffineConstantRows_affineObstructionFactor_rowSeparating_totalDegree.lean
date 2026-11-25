-- Prove2me | Theorems.Thm_HatAffineConstantRows_affineObstructionFactor_rowSeparating_totalDegree
-- name    : HatAffineConstantRows.affineObstructionFactor_rowSeparating_totalDegree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:09:55.654958+00:00
-- url     : https://prove2.me/theorems/27dae102-c64f-59b0-9c45-7b837774f88e
-- title:
--   Hat Affine Constant Rows: affine Obstruction Factor row Separating total Degree
-- statement:
--   The Hat Affine Constant Rows construction uses the affine Obstruction Factor row Separating total Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L152-L163
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L152-L163

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial

theorem HatAffineConstantRows.affineObstructionFactor_rowSeparating_totalDegree
    {K : Type u} [Field K] {m : Nat} {I : Type v}
    (A : I → Fin m → K) (b : I → K) (i : I) :
    (affineObstructionFactor A b (rowSeparatingOffset A b) i).totalDegree =
      rowDegree (A i) := by sorry
