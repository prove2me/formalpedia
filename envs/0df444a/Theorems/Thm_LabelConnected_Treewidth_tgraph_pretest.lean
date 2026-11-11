-- Prove2me | Theorems.Thm_LabelConnected_Treewidth_tgraph_pretest
-- name    : LabelConnected.Treewidth.tgraph_pretest
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:28:11.623581+00:00
-- url     : https://prove2.me/theorems/c29dd25b-843c-4a60-b47e-6b6655bb2254
-- title:
--   §6.1 T-graph pretest — G is a T-graph iff two connected spanning edge sets share at most one edge
-- statement:
--   The graph $G = (V, E)$ is a T-graph if and only if there are edge sets $E_1, E_2$ with $|E_1 \cap E_2| \le 1$ such that $(V, E_1)$ and $(V, E_2)$ are connected:
--   $$G \text{ T-graph} \iff \exists\, E_1, E_2 \subseteq E:\ |E_1 \cap E_2| \le 1,\ (V,E_1),\ (V,E_2) \text{ connected};$$
--   spanning trees $T_1 \subseteq E_1$, $T_2 \subseteq E_2$ of these two graphs then share at most one edge, i.e. form a T-witness.
--
--   This is the condition the first dynamic program of Theorem 6.2 checks: it only needs connectivity of two edge sets and a one-bit counter of shared edges.
--
--   Differences from the source:
--
--   - encoding: an undirected multigraph G = (V, E), parallel edges distinct, loops allowed → vertices Fin n, a finite edge type E and an endpoint map ends : E → Fin n × Fin n (a loop is an edge with equal endpoints, parallel edges are distinct edges with the same unordered endpoint pair); reason: Lean convention; every finite multigraph is one of these up to renaming
--   - encoding: (V, F) connected; a spanning tree / spanning forest of G → adjGraph ends F is Preconnected (the vertex-free graph counts as connected); a spanning tree is an edge set T with (V, T) a connected forest, a spanning forest an edge set with no cycle; reason: connectivity ignores loops and multiplicities; the only instance affected is n = 0, where every clause involved holds trivially
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), p. 26, §6.1, The T-Graph Pretest

import Mathlib
import Definitions.Def_LabelConnected_Treewidth_Multigraph
import Definitions.Def_LabelConnected_Treewidth_Witnesses

open Classical

namespace LabelConnected.Treewidth

/-- **§6.1, The T-Graph Pretest** (p. 26). `G` is a T-graph if and only if there are edge sets
`E₁, E₂` with `|E₁ ∩ E₂| ≤ 1` such that `(V, E₁)` and `(V, E₂)` are connected; and then spanning
trees `T₁ ⊆ E₁`, `T₂ ⊆ E₂` of these two graphs share at most one edge, i.e. form a T-witness. -/
theorem tgraph_pretest {n : ℕ} {E : Type} [Fintype E] [DecidableEq E] (ends : E → Fin n × Fin n) :
    (IsTGraph ends ↔
      ∃ E₁ E₂ : Finset E, (E₁ ∩ E₂).card ≤ 1 ∧ SpansConnected ends E₁ ∧ SpansConnected ends E₂) ∧
    ∀ E₁ E₂ T₁ T₂ : Finset E, (E₁ ∩ E₂).card ≤ 1 → SpansConnected ends E₁ →
      SpansConnected ends E₂ → T₁ ⊆ E₁ → T₂ ⊆ E₂ → IsSpanningTree ends T₁ →
      IsSpanningTree ends T₂ → IsTWitness ends T₁ T₂ := by sorry

end LabelConnected.Treewidth
