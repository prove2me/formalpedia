-- Prove2me | Theorems.Thm_LabelConnected_Treewidth_theorem_4_1
-- name    : LabelConnected.Treewidth.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:28:09.495485+00:00
-- url     : https://prove2.me/theorems/fda2405c-c69b-490d-8ea8-3594876872fd
-- title:
--   Theorem 4.1 — a multigraph is label-connected iff it has at most one vertex, is a T-graph, or is an M-graph
-- statement:
--   Let $G$ be a multigraph on $n$ vertices. Then $G$ is a yes-instance of Gossiping (some temporal labeling makes it temporally connected) if and only if at least one of the following holds: $G$ has at most one vertex; $G$ is a T-graph (two spanning trees sharing at most one edge); $G$ is an M-graph (it admits an M-witness and is not a T-graph):
--   $$G \text{ label-connected} \iff n \le 1 \ \lor\ G \text{ is a T-graph} \ \lor\ G \text{ is an M-graph}.$$
--
--   This classical characterization (Burosch–Laborde, Bumby, Krumme; proved in Appendix A of the paper) is what every algorithm of the paper searches for: a yes-instance is recognized by finding a T-witness or an M-witness.
--
--   Differences from the source:
--
--   - encoding: an undirected multigraph G = (V, E), parallel edges distinct, loops allowed → vertices Fin n, a finite edge type E and an endpoint map ends : E → Fin n × Fin n (a loop is an edge with equal endpoints, parallel edges are distinct edges with the same unordered endpoint pair); reason: Lean convention; every finite multigraph is one of these up to renaming
--   - encoding: (V, F) connected; a spanning tree / spanning forest of G → adjGraph ends F is Preconnected (the vertex-free graph counts as connected); a spanning tree is an edge set T with (V, T) a connected forest, a spanning forest an edge set with no cycle; reason: connectivity ignores loops and multiplicities; the only instance affected is n = 0, where every clause involved holds trivially
--   - encoding: a cycle v0e1v1···eℓvℓ of G, identified with its subgraph → a Cycle ends: length len ≥ 1, injective vertex map vert : Fin len → Fin n, injective edge map edge : Fin len → E, edge i joining vert i and vert (i + 1 mod len); E(C) and V(C) are the images; reason: the paper's own definition (p. 6) as a cyclic sequence
--   - encoding: λ: E → N assigning one positive integer to each edge → lab : E → ℕ with 0 < lab e for every edge e; reason: ℕ contains 0 in Lean
--   - encoding: a strict temporal path traversing edges e1, …, eℓ with λ(e1) < ··· < λ(eℓ), paths without repeated vertices, length 0 allowed → ℓ ∈ ℕ, an injective vertex sequence v : Fin (ℓ+1) → Fin n from u to w, edges e i joining v i and v (i+1), labels strictly increasing; reason: the paper's path convention (p. 6) written out
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), p. 15, Theorem 4.1

import Mathlib
import Definitions.Def_LabelConnected_Treewidth_Multigraph
import Definitions.Def_LabelConnected_Treewidth_Temporal
import Definitions.Def_LabelConnected_Treewidth_Witnesses

open Classical

namespace LabelConnected.Treewidth

/-- **Theorem 4.1** ([14, 15, 49]). A multigraph `G` is a yes-instance of Gossiping if and only if
it has at most one vertex, or it is a T-graph, or it is an M-graph. -/
theorem theorem_4_1 {n : ℕ} {E : Type} [Fintype E] [DecidableEq E] (ends : E → Fin n × Fin n) :
    IsLabelConnected ends ↔ n ≤ 1 ∨ IsTGraph ends ∨ IsMGraph ends := by sorry

end LabelConnected.Treewidth
