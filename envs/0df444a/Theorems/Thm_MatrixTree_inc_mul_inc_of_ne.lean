-- Prove2me | Theorems.Thm_MatrixTree_inc_mul_inc_of_ne
-- name    : MatrixTree.inc_mul_inc_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:05:42.410814+00:00
-- url     : https://prove2.me/theorems/f1b7ed51-700d-5087-8303-6ea3e1441243
-- title:
--   Matrix Tree: inc mul inc of ne
-- statement:
--   The Matrix Tree construction uses the inc mul inc of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L163-L169
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L163-L169

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

theorem MatrixTree.inc_mul_inc_of_ne {e : Sym2 V} (he : ¬ e.IsDiag) {x y : V} (hxy : x ≠ y) (hx : x ∈ e)
    (hy : y ∈ e) : inc e x * inc e y = -1 := by sorry
