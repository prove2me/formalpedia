-- Prove2me | Theorems.Thm_MatrixTree_isUnit_det_incMat_of_isTree
-- name    : MatrixTree.isUnit_det_incMat_of_isTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:07:00.987839+00:00
-- url     : https://prove2.me/theorems/815bbd2f-857c-4bf7-9278-072de5d23e65
-- title:
--   Matrix Tree: is Unit det inc Mat of is Tree
-- statement:
--   The Matrix Tree construction uses the is Unit det inc Mat of is Tree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L245-L317
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L245-L317

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem MatrixTree.isUnit_det_incMat_of_isTree (v : V) (g : {u // u ≠ v} → Sym2 V)
    (hg : ∀ w, ¬ (g w).IsDiag) (hT : (fromEdgeSet (Set.range g)).IsTree) :
    IsUnit (incMat v g).det := by sorry
