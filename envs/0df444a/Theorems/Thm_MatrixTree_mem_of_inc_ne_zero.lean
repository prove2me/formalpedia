-- Prove2me | Theorems.Thm_MatrixTree_mem_of_inc_ne_zero
-- name    : MatrixTree.mem_of_inc_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T11:01:07.260881+00:00
-- url     : https://prove2.me/theorems/0304a4b5-8d93-5608-8879-1564ad2a4ac9
-- title:
--   Matrix Tree: mem of inc ne zero
-- statement:
--   The Matrix Tree construction uses the mem of inc ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L147-L148
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L147-L148

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

theorem MatrixTree.mem_of_inc_ne_zero {e : Sym2 V} {x : V} (hx : inc e x ≠ 0) : x ∈ e := by sorry
