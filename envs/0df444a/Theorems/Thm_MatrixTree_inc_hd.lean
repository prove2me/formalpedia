-- Prove2me | Theorems.Thm_MatrixTree_inc_hd
-- name    : MatrixTree.inc_hd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:56:14.481696+00:00
-- url     : https://prove2.me/theorems/160fcede-35ee-4728-95e9-8b8e75832f4b
-- title:
--   Matrix Tree: inc hd
-- statement:
--   The Matrix Tree construction uses the inc hd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L140-L141
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L140-L141

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*}
variable [DecidableEq V]

theorem MatrixTree.inc_hd {e : Sym2 V} (he : ¬ e.IsDiag) : inc e (hd e) = -1 := by sorry
