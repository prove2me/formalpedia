-- Prove2me | Theorems.Thm_LabelConnected_Treewidth_lemma_6_1
-- name    : LabelConnected.Treewidth.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:29:10.078221+00:00
-- url     : https://prove2.me/theorems/ab386138-5e79-4f50-a012-924eb746b2cb
-- title:
--   Lemma 6.1 — relaxed M-witnesses: at most four components per edge set, each meeting the cycle; an M-witness in O(n + m)
-- statement:
--   A multigraph $G$ admits an M-witness if and only if there are pairwise disjoint edge sets $C, D_1, D_2 \subseteq E(G)$ such that $C$ is the edge set of a cycle of length at least four and, for each $i \in \{1, 2\}$, the graph $(V(G), D_i)$ has at most four components, each of which meets $V(C)$:
--   $$\exists\,(C, F_1, F_2)\ \text{M-witness} \iff \exists\, C, D_1, D_2 \text{ disjoint}:\ C = E(\text{cycle of length} \ge 4),\ \#\mathrm{comp}(V, D_i) \le 4,\ \text{each component meets } V(C).$$
--   Moreover, given such sets, an M-witness can be computed in $O(n + m)$ time: one deterministic word-RAM program and constants $K, W$, fixed before the input, which on $G$ followed by the lists of $C, D_1, D_2$ halts within $K(n+m) + K$ steps, registers within $W(1 + \log_2(2 + n + m))$ bits, and outputs $E(C'), F_1, F_2$ of an M-witness of $G$.
--
--   The relaxation removes the exact component count from the search: in the dynamic program of Theorem 6.2 it is enforced through at most four apex edges.
--
--   Differences from the source:
--
--   - encoding: an undirected multigraph G = (V, E), parallel edges distinct, loops allowed → vertices Fin n, a finite edge type E and an endpoint map ends : E → Fin n × Fin n (a loop is an edge with equal endpoints, parallel edges are distinct edges with the same unordered endpoint pair); reason: Lean convention; every finite multigraph is one of these up to renaming
--   - encoding: (V, F) connected; a spanning tree / spanning forest of G → adjGraph ends F is Preconnected (the vertex-free graph counts as connected); a spanning tree is an edge set T with (V, T) a connected forest, a spanning forest an edge set with no cycle; reason: connectivity ignores loops and multiplicities; the only instance affected is n = 0, where every clause involved holds trivially
--   - encoding: a cycle v0e1v1···eℓvℓ of G, identified with its subgraph → a Cycle ends: length len ≥ 1, injective vertex map vert : Fin len → Fin n, injective edge map edge : Fin len → E, edge i joining vert i and vert (i + 1 mod len); E(C) and V(C) are the images; reason: the paper's own definition (p. 6) as a cyclic sequence
--   - encoding: computed in O(n + m) time on the word RAM with Θ(log(n+m))-bit words → one deterministic program of the published integer RAM CongruencyTU (no coin, no query) and constants fixed before the input; every register at every step within W·(1 + ⌊log₂(2 + n + m)⌋) bits; halting within K·(n + m) + K steps; reason: O(·) as explicit universal constants on one fixed machine; the word bound keeps unit-cost arithmetic honest
--   - encoding: the input multigraph (and edge sets / witnesses handed to the algorithm) → [n, m, u1, v1, …, um, vm] (MinDegST.AddOne.encGraph), edge e_i referred to by its index i − 1, an edge set as its length followed by its indices, each once, in any order; reason: a running time needs a fixed input representation; the edge-list representation is the paper's (p. 18, proof of Lemma 5.1)
--   - encoding: an M-witness is computed → the output lists E(C'), F1, F2 of some M-witness (C', F1, F2) of G (the cycle by its edge set); reason: a cycle of length ≥ 3 is determined by its edge set
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), p. 25, Lemma 6.1

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Machine
import Definitions.Def_LabelConnected_Treewidth_Multigraph
import Definitions.Def_LabelConnected_Treewidth_Witnesses
import Definitions.Def_LabelConnected_Treewidth_Encoding

open Classical

namespace LabelConnected.Treewidth

/-- **Lemma 6.1.** (i) A multigraph `G` admits an M-witness if and only if there are pairwise
disjoint edge sets `C, D₁, D₂ ⊆ E(G)` such that `C` is the edge set of a cycle of length at least
four and, for each `i ∈ {1, 2}`, the graph `(V(G), Dᵢ)` has at most four components, each of which
meets `V(C)`. (ii) Moreover, one deterministic word-RAM program and constants `K, W`, fixed before
the input, compute an M-witness from such sets: on input `G` followed by the lists of `C, D₁, D₂`,
registers stay within `W · (1 + log₂(2 + n + m))` bits and the program halts within
`K·(n + m) + K` steps with an M-witness `(E(C'), F₁, F₂)` of `G` as output. -/
theorem lemma_6_1 :
    (∀ {n : ℕ} {E : Type} [Fintype E] [DecidableEq E] (ends : E → Fin n × Fin n),
      HasMWitness ends ↔
        ∃ (C D₁ D₂ : Finset E) (c : Cycle ends),
          Disjoint C D₁ ∧ Disjoint C D₂ ∧ Disjoint D₁ D₂ ∧
          4 ≤ c.len ∧ c.edgeSet = C ∧
          (∀ D ∈ ({D₁, D₂} : Finset (Finset E)),
            numComponents ends D ≤ 4 ∧
            ∀ K : (adjGraph ends (D : Set E)).ConnectedComponent,
              ∃ v ∈ c.vertSet, compOf ends D v = K)) ∧
    ∃ (P : CongruencyTU.Program) (K W : ℕ), MinDegST.AddOne.Deterministic P ∧
      ∀ (n : ℕ) (es : List (Fin n × Fin n)) (C D₁ D₂ : Finset (Fin es.length))
        (c : Cycle (ofList es)) (lC l₁ l₂ : List (Fin es.length)),
        Disjoint C D₁ → Disjoint C D₂ → Disjoint D₁ D₂ →
        4 ≤ c.len → c.edgeSet = C →
        (∀ D ∈ ({D₁, D₂} : Finset (Finset (Fin es.length))),
          numComponents (ofList es) D ≤ 4 ∧
          ∀ K : (adjGraph (ofList es) (D : Set (Fin es.length))).ConnectedComponent,
            ∃ v ∈ c.vertSet, compOf (ofList es) D v = K) →
        ListsSet lC C → ListsSet l₁ D₁ → ListsSet l₂ D₂ →
        MinDegST.AddOne.WordBounded P (encThreeSetsInput n es lC l₁ l₂) W (n + es.length) ∧
        MinDegST.AddOne.HaltsWithin P (encThreeSetsInput n es lC l₁ l₂)
          ((K : ℝ) * ((n : ℝ) + (es.length : ℝ)) + K) (IsMWitnessOutput es) := by sorry

end LabelConnected.Treewidth
