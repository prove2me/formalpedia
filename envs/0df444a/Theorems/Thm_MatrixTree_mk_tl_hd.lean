-- Prove2me | Theorems.Thm_MatrixTree_mk_tl_hd
-- name    : MatrixTree.mk_tl_hd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:56:19.235783+00:00
-- url     : https://prove2.me/theorems/82ca8b0c-071d-4573-ad59-413af41b3fa0
-- title:
--   Matrix Tree: mk tl hd
-- statement:
--   The Matrix Tree construction uses the mk tl hd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L123-L123
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L123-L123

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*}

theorem MatrixTree.mk_tl_hd (e : Sym2 V) : s(tl e, hd e) = e := by sorry
