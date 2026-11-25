-- Prove2me | Theorems.Thm_HatAffineConstantRows_rowSeparating_obstruction_totalDegree_lt
-- name    : HatAffineConstantRows.rowSeparating_obstruction_totalDegree_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:10:15.549801+00:00
-- url     : https://prove2.me/theorems/5209573c-efcf-456b-853c-0b8e5d1950c0
-- title:
--   Hat Affine Constant Rows: row Separating obstruction total Degree lt
-- statement:
--   The Hat Affine Constant Rows construction uses the row Separating obstruction total Degree lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L218-L230
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L218-L230

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial

theorem HatAffineConstantRows.rowSeparating_obstruction_totalDegree_lt
    {K : Type u} [Field K] {m : Nat} {I : Type v} [Fintype I]
    (A : I → Fin m → K) (b : I → K)
    (i0 : I) (hi0 : A i0 = 0) :
    (affineObstruction A b (rowSeparatingOffset A b)).totalDegree <
      Fintype.card I := by sorry
