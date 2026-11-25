-- Prove2me | Theorems.Thm_NashWilliams_exists_trees_of_isEdgeConnected
-- name    : NashWilliams.exists_trees_of_isEdgeConnected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:46:07.043994+00:00
-- url     : https://prove2.me/theorems/98cd42e3-13b4-413e-8ec3-d0ff970817ba
-- title:
--   Nash Williams: exists trees of is Edge Connected
-- statement:
--   **Corollary.** A finite `2k`-edge-connected graph on a nonempty vertex type has `k` pairwise
--   edge-disjoint spanning trees.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliams.lean#L189-L231
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliams.lean#L189-L231

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Definitions.Def_TreePackingLib_NashWilliams
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph
open NashWilliams

theorem NashWilliams.exists_trees_of_isEdgeConnected {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (k : ℕ) (hG : G.IsEdgeConnected (2 * k)) :
    ∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
      Pairwise fun i j ↦ Disjoint (T i) (T j) := by sorry
