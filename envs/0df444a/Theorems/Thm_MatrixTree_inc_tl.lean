-- Prove2me | Theorems.Thm_MatrixTree_inc_tl
-- name    : MatrixTree.inc_tl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:55:46.726551+00:00
-- url     : https://prove2.me/theorems/8bfbd23e-e41b-59eb-ae18-6bc02ba053c2
-- title:
--   Matrix Tree: inc tl
-- statement:
--   The Matrix Tree construction uses the inc tl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L138-L138
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L138-L138

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

theorem MatrixTree.inc_tl (e : Sym2 V) : inc e (tl e) = 1 := by sorry
