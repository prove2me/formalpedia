-- Prove2me | Theorems.Thm_MatrixTree_inc_mul_self
-- name    : MatrixTree.inc_mul_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T11:01:27.930561+00:00
-- url     : https://prove2.me/theorems/4e2958a8-2334-4d84-8a03-7e9af73f2910
-- title:
--   Matrix Tree: inc mul self
-- statement:
--   The Matrix Tree construction uses the inc mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L155-L161
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L155-L161

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

theorem MatrixTree.inc_mul_self {e : Sym2 V} (he : ¬ e.IsDiag) (x : V) :
    inc e x * inc e x = if x ∈ e then 1 else 0 := by sorry
