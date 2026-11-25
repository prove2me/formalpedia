-- Prove2me | Theorems.Thm_HatAffineConstantRows_rowSeparating_obstruction_totalDegree
-- name    : HatAffineConstantRows.rowSeparating_obstruction_totalDegree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:10:03.3928+00:00
-- url     : https://prove2.me/theorems/b081b1b4-956f-5ea1-91aa-216be501f687
-- title:
--   Hat Affine Constant Rows: row Separating obstruction total Degree
-- statement:
--   The Hat Affine Constant Rows construction uses the row Separating obstruction total Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L194-L216
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L194-L216

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial

theorem HatAffineConstantRows.rowSeparating_obstruction_totalDegree
    {K : Type u} [Field K] {m : Nat} {I : Type v} [Fintype I]
    (A : I → Fin m → K) (b : I → K) :
    (affineObstruction A b (rowSeparatingOffset A b)).totalDegree =
      nonzeroRowCount A := by sorry
