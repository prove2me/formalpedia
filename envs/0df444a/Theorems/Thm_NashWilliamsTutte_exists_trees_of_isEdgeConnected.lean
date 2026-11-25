-- Prove2me | Theorems.Thm_NashWilliamsTutte_exists_trees_of_isEdgeConnected
-- name    : NashWilliamsTutte.exists_trees_of_isEdgeConnected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:35:44.079228+00:00
-- url     : https://prove2.me/theorems/88bf2417-8460-4a3e-9536-9953cbe9c4f9
-- title:
--   Nash Williams Tutte: exists trees of is Edge Connected
-- statement:
--   **Corollary.** A finite `2k`-edge-connected graph on a nonempty vertex type has `k` pairwise
--   edge-disjoint spanning trees.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/Solution.lean#L50-L54
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/Solution.lean#L50-L54

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliams
public import Definitions.Def_NashWilliamsTrees_Solution
public import Theorems.Thm_NashWilliams_exists_trees_of_isEdgeConnected

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph
open NashWilliamsTutte

theorem NashWilliamsTutte.exists_trees_of_isEdgeConnected {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (k : ℕ) (hG : G.IsEdgeConnected (2 * k)) :
    ∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
      Pairwise fun i j ↦ Disjoint (T i) (T j) := by sorry
