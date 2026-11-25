-- Prove2me | Theorems.Thm_MatrixTree_isUnit_inc
-- name    : MatrixTree.isUnit_inc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T11:01:22.755887+00:00
-- url     : https://prove2.me/theorems/841f1a81-d093-446b-b321-671023689bbe
-- title:
--   Matrix Tree: is Unit inc
-- statement:
--   The Matrix Tree construction uses the is Unit inc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L150-L153
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L150-L153

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

theorem MatrixTree.isUnit_inc {e : Sym2 V} (he : ¬ e.IsDiag) {x : V} (hx : x ∈ e) : IsUnit (inc e x) := by sorry
