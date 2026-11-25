-- Prove2me | Theorems.Thm_MatrixTree_det_incMat_eq_zero_of_not_reachable
-- name    : MatrixTree.det_incMat_eq_zero_of_not_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:06:27.748896+00:00
-- url     : https://prove2.me/theorems/eb406893-3830-4ffe-abbe-369ecfaae132
-- title:
--   Matrix Tree: det inc Mat eq zero of not reachable
-- statement:
--   The Matrix Tree construction uses the det inc Mat eq zero of not reachable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L211-L243
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L211-L243

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem MatrixTree.det_incMat_eq_zero_of_not_reachable (v : V) (g : {u // u ≠ v} → Sym2 V)
    (hg : ∀ w, ¬ (g w).IsDiag) (u : V) (hu : ¬ (fromEdgeSet (Set.range g)).Reachable v u) :
    (incMat v g).det = 0 := by sorry
