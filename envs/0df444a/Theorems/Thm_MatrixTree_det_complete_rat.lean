-- Prove2me | Theorems.Thm_MatrixTree_det_complete_rat
-- name    : MatrixTree.det_complete_rat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:11:42.866693+00:00
-- url     : https://prove2.me/theorems/d09a2163-0666-5e8b-abbe-a832c11d7537
-- title:
--   Matrix Tree: det complete rat
-- statement:
--   The Matrix Tree construction uses the det complete rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L477-L498
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L477-L498

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree

theorem MatrixTree.det_complete_rat {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (Matrix.of fun i j : ι => if i = j then (Fintype.card ι : ℚ) else -1).det =
      ((Fintype.card ι : ℚ) + 1) ^ (Fintype.card ι - 1) := by sorry
