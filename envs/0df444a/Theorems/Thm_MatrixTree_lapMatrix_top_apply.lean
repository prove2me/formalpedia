-- Prove2me | Theorems.Thm_MatrixTree_lapMatrix_top_apply
-- name    : MatrixTree.lapMatrix_top_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:12:13.615783+00:00
-- url     : https://prove2.me/theorems/b7941f44-1d46-4bb0-8864-b1fcf6770ff3
-- title:
--   Matrix Tree: lap Matrix top apply
-- statement:
--   The Matrix Tree construction uses the lap Matrix top apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L517-L528
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L517-L528

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree

theorem MatrixTree.lapMatrix_top_apply (n : ℕ) (x y : Fin n) :
    (⊤ : SimpleGraph (Fin n)).lapMatrix ℤ x y = if x = y then ((n : ℤ) - 1) else -1 := by sorry
