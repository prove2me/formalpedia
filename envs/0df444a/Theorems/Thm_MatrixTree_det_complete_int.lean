-- Prove2me | Theorems.Thm_MatrixTree_det_complete_int
-- name    : MatrixTree.det_complete_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:12:10.062576+00:00
-- url     : https://prove2.me/theorems/a36d07cb-5c06-4824-8894-8342c8a3cf54
-- title:
--   Matrix Tree: det complete int
-- statement:
--   The Matrix Tree construction uses the det complete int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L500-L515
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L500-L515

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree

theorem MatrixTree.det_complete_int {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (Matrix.of fun i j : ι => if i = j then (Fintype.card ι : ℤ) else -1).det =
      ((Fintype.card ι : ℤ) + 1) ^ (Fintype.card ι - 1) := by sorry
