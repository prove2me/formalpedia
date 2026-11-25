-- Prove2me | Theorems.Thm_MatrixTree_det_incMat_sq_of_isTree
-- name    : MatrixTree.det_incMat_sq_of_isTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:06:52.851794+00:00
-- url     : https://prove2.me/theorems/c61d21db-b3f2-4e7d-aed6-f85f060a89a7
-- title:
--   Matrix Tree: det inc Mat sq of is Tree
-- statement:
--   The Matrix Tree construction uses the det inc Mat sq of is Tree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L328-L331
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L328-L331

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem MatrixTree.det_incMat_sq_of_isTree (v : V) (g : {u // u ≠ v} → Sym2 V) (hg : ∀ w, ¬ (g w).IsDiag)
    (hT : (fromEdgeSet (Set.range g)).IsTree) : (incMat v g).det ^ 2 = 1 := by sorry
