-- Prove2me | Theorems.Thm_MatrixTree_fromEdgeSet_adj_tl_hd
-- name    : MatrixTree.fromEdgeSet_adj_tl_hd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:56:01.342138+00:00
-- url     : https://prove2.me/theorems/c141b664-2c9a-5bb9-b5fb-d147466a3551
-- title:
--   Matrix Tree: from Edge Set adj tl hd
-- statement:
--   The Matrix Tree construction uses the from Edge Set adj tl hd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L200-L203
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L200-L203

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem MatrixTree.fromEdgeSet_adj_tl_hd (v : V) (g : {u // u ≠ v} → Sym2 V) (hg : ∀ w, ¬ (g w).IsDiag)
    (w : {u // u ≠ v}) : (fromEdgeSet (Set.range g)).Adj (tl (g w)) (hd (g w)) := by sorry
