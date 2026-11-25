-- Prove2me | Theorems.Thm_MatrixTree_det_incMat_eq_zero_of_not_isTree
-- name    : MatrixTree.det_incMat_eq_zero_of_not_isTree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T11:06:07.457892+00:00
-- url     : https://prove2.me/theorems/5deaf1de-197c-50b4-8ff3-9ec5fc7687a5
-- title:
--   Matrix Tree: det inc Mat eq zero of not is Tree
-- statement:
--   The Matrix Tree construction uses the det inc Mat eq zero of not is Tree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L333-L350
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L333-L350

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem MatrixTree.det_incMat_eq_zero_of_not_isTree (v : V) (g : {u // u ≠ v} → Sym2 V)
    (hg : ∀ w, ¬ (g w).IsDiag) (hT : ¬ (fromEdgeSet (Set.range g)).IsTree) :
    (incMat v g).det = 0 := by sorry
