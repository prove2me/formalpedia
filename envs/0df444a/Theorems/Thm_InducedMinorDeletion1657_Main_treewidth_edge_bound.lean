-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_treewidth_edge_bound
-- name    : InducedMinorDeletion1657.Main.treewidth_edge_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:35:26.198538+00:00
-- url     : https://prove2.me/theorems/cf880ed8-fa17-42e9-89b7-957c3dde7b62
-- title:
--   Lemma 3.10 — treewidth from edge count
-- statement:
--   For every fixed finite graph $H$ there is a positive constant $C$, depending only on $H$, such that every $H$-induced-minor-free graph $G$ satisfies
--   $$\operatorname{tw}(G)\le C\sqrt{|E(G)|}.$$
--   The constant precedes the graph quantifier. This is the structural edge bound using the repaired separator theorem cited in the source, with no separator or sparsity assumption supplied as a hypothesis.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - encoding: O(√|E(G)|) → ∃ positive natural C before every G, with a real square root; reason: the ceiling of a uniform positive real constant changes no instance; edge counts are nonnegative
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 15 (PDF p. 16), Lemma 3.10

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Lemma 3.10, printed p. 15 / PDF p. 16. See the local source audit for conventions. -/
theorem treewidth_edge_bound :
∀ H : InputGraph, ∃ C : ℕ, 0 < C ∧ ∀ G : InputGraph,
  excluded H.graph G.graph →
  (width G.graph : ℝ) ≤ C * Real.sqrt (edges G.graph : ℝ) := by sorry

end InducedMinorDeletion1657.Main
