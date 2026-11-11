-- Prove2me | Theorems.Thm_LabelConnected_Treewidth_apex_formulation
-- name    : LabelConnected.Treewidth.apex_formulation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:28:19.999511+00:00
-- url     : https://prove2.me/theorems/a27322d2-2bb1-41f1-a777-d67ccf5e5a57
-- title:
--   §6.1 M-witness formulation — solutions (C, D1, D2, A) of the apex formulation exist iff an M-witness does (G not a T-graph)
-- statement:
--   Add an apex $a$ joined to every vertex $v$ by an apex edge $av$. A solution is a tuple $(C, D_1, D_2, A)$ of pairwise disjoint sets $C, D_1, D_2$ of original edges and a common set $A$ of apex edges such that (1) $C$ is the edge set of a connected 2-regular graph with at least four vertices; (2) every apex edge in $A$ ends at a vertex of $C$, and $|A| \le 4$; (3) $\widehat G_i = (V \cup \{a\}, D_i \cup A)$ is connected for $i \in \{1, 2\}$. When the T-graph pretest has rejected ($G$ is not a T-graph), these conditions are equivalent to the existence of an M-witness:
--   $$G \text{ not a T-graph} \implies \big(\exists \text{ M-witness} \iff \exists\,(C, D_1, D_2, A) \text{ solution}\big),$$
--   and every solution yields an M-witness whether or not $G$ is a T-graph.
--
--   This is the formulation the second dynamic program of Theorem 6.2 decides; only connectivity, degrees and two small counters remain to be tracked.
--
--   Differences from the source:
--
--   - encoding: an undirected multigraph G = (V, E), parallel edges distinct, loops allowed → vertices Fin n, a finite edge type E and an endpoint map ends : E → Fin n × Fin n (a loop is an edge with equal endpoints, parallel edges are distinct edges with the same unordered endpoint pair); reason: Lean convention; every finite multigraph is one of these up to renaming
--   - encoding: (V, F) connected; a spanning tree / spanning forest of G → adjGraph ends F is Preconnected (the vertex-free graph counts as connected); a spanning tree is an edge set T with (V, T) a connected forest, a spanning forest an edge set with no cycle; reason: connectivity ignores loops and multiplicities; the only instance affected is n = 0, where every clause involved holds trivially
--   - encoding: a cycle v0e1v1···eℓvℓ of G, identified with its subgraph → a Cycle ends: length len ≥ 1, injective vertex map vert : Fin len → Fin n, injective edge map edge : Fin len → E, edge i joining vert i and vert (i + 1 mod len); E(C) and V(C) are the images; reason: the paper's own definition (p. 6) as a cyclic sequence
--   - encoding: the apex a and apex edges av; Ĝi = (V ∪ {a}, Di ∪ A) → vertex type Option (Fin n) with a = none, A ⊆ Fin n (apex edge av ↔ v), Ĝi the simple graph apexGraph ends Di A; reason: apex edges are determined by their original endpoint; connectivity ignores multiplicities
--   - generalization: for G not a T-graph (the pretest rejected), the conditions are equivalent to the existence of an M-witness → the same equivalence under ¬ IsTGraph, plus the direction solution ⇒ M-witness for every G; reason: the page proves that direction without the pretest ("If the conditions hold, every component of (V, Di) meets V(C) …", then Lemma 6.1); with ¬ IsTGraph it is the printed equivalence
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), p. 27, §6.1, The M-Witness Formulation

import Mathlib
import Definitions.Def_LabelConnected_Treewidth_Multigraph
import Definitions.Def_LabelConnected_Treewidth_Witnesses
import Definitions.Def_LabelConnected_Treewidth_Apex

open Classical

namespace LabelConnected.Treewidth

/-- **§6.1, The M-Witness Formulation** (p. 27). Add an apex `a` joined to every vertex by an apex
edge. A solution is `(C, D₁, D₂, A)`: pairwise disjoint sets `C, D₁, D₂` of original edges and a set
`A` of apex edges with (1) `C` the edge set of a connected 2-regular graph with at least four
vertices, (2) every apex edge of `A` ending at a vertex of `C` and `|A| ≤ 4`, (3)
`Ĝᵢ = (V ∪ {a}, Dᵢ ∪ A)` connected for `i = 1, 2`. Every solution yields an M-witness; and if `G`
is not a T-graph (the pretest rejected), then `G` admits an M-witness if and only if a solution
exists. -/
theorem apex_formulation {n : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (ends : E → Fin n × Fin n) :
    (∀ (C D₁ D₂ : Finset E) (A : Finset (Fin n)),
      IsApexSolution ends C D₁ D₂ A → HasMWitness ends) ∧
    (¬ IsTGraph ends →
      (HasMWitness ends ↔
        ∃ (C D₁ D₂ : Finset E) (A : Finset (Fin n)), IsApexSolution ends C D₁ D₂ A)) := by sorry

end LabelConnected.Treewidth
