-- Prove2me | Theorems.Thm_MatrixTree_mem_iff_tl_or_hd
-- name    : MatrixTree.mem_iff_tl_or_hd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:55:53.286965+00:00
-- url     : https://prove2.me/theorems/54f0f661-7100-468b-a1fc-247c61359891
-- title:
--   Matrix Tree: mem iff tl or hd
-- statement:
--   The Matrix Tree construction uses the mem iff tl or hd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L128-L130
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L128-L130

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*}

theorem MatrixTree.mem_iff_tl_or_hd {e : Sym2 V} {x : V} : x ∈ e ↔ x = tl e ∨ x = hd e := by sorry
