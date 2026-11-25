-- Prove2me | Theorems.Thm_MatrixTree_lapMatrix_eq_sum
-- name    : MatrixTree.lapMatrix_eq_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T11:06:36.957161+00:00
-- url     : https://prove2.me/theorems/b887df8d-bc63-40b2-871c-d6bb1a674904
-- title:
--   Matrix Tree: lap Matrix eq sum
-- statement:
--   The Matrix Tree construction uses the lap Matrix eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L355-L379
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L355-L379

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree

theorem MatrixTree.lapMatrix_eq_sum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y : V) :
    G.lapMatrix ℤ x y = ∑ e ∈ G.edgeFinset, inc e x * inc e y := by sorry
