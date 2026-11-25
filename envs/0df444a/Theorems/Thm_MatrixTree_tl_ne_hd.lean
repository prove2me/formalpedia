-- Prove2me | Theorems.Thm_MatrixTree_tl_ne_hd
-- name    : MatrixTree.tl_ne_hd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:56:08.346677+00:00
-- url     : https://prove2.me/theorems/47de0f47-eec6-4b4b-92e3-b3fa14184eef
-- title:
--   Matrix Tree: tl ne hd
-- statement:
--   The Matrix Tree construction uses the tl ne hd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L125-L126
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L125-L126

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*}

theorem MatrixTree.tl_ne_hd {e : Sym2 V} (he : ¬ e.IsDiag) : tl e ≠ hd e := by sorry
