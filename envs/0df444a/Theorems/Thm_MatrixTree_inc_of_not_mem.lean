-- Prove2me | Theorems.Thm_MatrixTree_inc_of_not_mem
-- name    : MatrixTree.inc_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:55:55.08133+00:00
-- url     : https://prove2.me/theorems/04f69987-8fc5-52ac-8c95-a1ce84b43017
-- title:
--   Matrix Tree: inc of not mem
-- statement:
--   The Matrix Tree construction uses the inc of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L143-L145
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L143-L145

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

theorem MatrixTree.inc_of_not_mem {e : Sym2 V} {x : V} (hx : x ∉ e) : inc e x = 0 := by sorry
