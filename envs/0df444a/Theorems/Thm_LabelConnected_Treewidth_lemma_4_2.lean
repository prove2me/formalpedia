-- Prove2me | Theorems.Thm_LabelConnected_Treewidth_lemma_4_2
-- name    : LabelConnected.Treewidth.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:28:02.784745+00:00
-- url     : https://prove2.me/theorems/52da9c7a-3688-42ff-805f-5a3712995558
-- title:
--   Lemma 4.2 — common four intervals and alternating matchings of an M-witness of an M-graph
-- statement:
--   Let $G$ be an M-graph and $(C, F_1, F_2)$ an M-witness of $G$. There is a partition of $V(C)$ into four nonempty consecutive intervals $X_1, X_2, X_3, X_4$ of the cycle, indexed in cyclic order, with:
--
--   * **Common intervals.** For each forest $F_j$, the intersections of its four components with $V(C)$ are exactly $X_1, X_2, X_3, X_4$.
--   * **Alternating matchings.** Let $b_i$ be the cycle edge joining $X_i$ to $X_{i+1}$ (indices modulo four). Then $B_1 = \{b_1, b_3\}$ and $B_2 = \{b_2, b_4\}$ are edge-disjoint matchings, and every component of each forest contains exactly one vertex of $V(B_1)$ and exactly one vertex of $V(B_2)$.
--
--   In the Lean statement the cycle is $v_0 v_1 \cdots v_{\ell-1}$ with edge $\mathrm{edgeAt}(k)$ joining $v_k$ and $v_{k+1}$; the intervals are
--   $$X_i = \{\, v_{r+j} : k_i \le j < k_{i+1} \,\},\qquad 0 = k_0 < k_1 < k_2 < k_3 < k_4 = \ell,$$
--   for $i = 0,1,2,3$ (the paper's $X_1, \dots, X_4$), and $b_i = \mathrm{edgeAt}(r + k_{i+1} - 1)$, the edge from the last vertex of $X_i$ to the first of $X_{i+1}$.
--
--   The lemma gives both forests four common roots on the cycle; it is what turns an M-witness into the apex formulation of Theorem 6.2 and into the labeling of Lemma 4.4.
--
--   Differences from the source:
--
--   - encoding: an undirected multigraph G = (V, E), parallel edges distinct, loops allowed → vertices Fin n, a finite edge type E and an endpoint map ends : E → Fin n × Fin n (a loop is an edge with equal endpoints, parallel edges are distinct edges with the same unordered endpoint pair); reason: Lean convention; every finite multigraph is one of these up to renaming
--   - encoding: (V, F) connected; a spanning tree / spanning forest of G → adjGraph ends F is Preconnected (the vertex-free graph counts as connected); a spanning tree is an edge set T with (V, T) a connected forest, a spanning forest an edge set with no cycle; reason: connectivity ignores loops and multiplicities; the only instance affected is n = 0, where every clause involved holds trivially
--   - encoding: a cycle v0e1v1···eℓvℓ of G, identified with its subgraph → a Cycle ends: length len ≥ 1, injective vertex map vert : Fin len → Fin n, injective edge map edge : Fin len → E, edge i joining vert i and vert (i + 1 mod len); E(C) and V(C) are the images; reason: the paper's own definition (p. 6) as a cyclic sequence
--   - encoding: a partition of V(C) into four nonempty consecutive intervals X1, …, X4 indexed in cyclic order; bi the cycle edge joining Xi to Xi+1 → a start index r and breakpoints 0 = k0 < k1 < k2 < k3 < k4 = len with Xi the images of [ki, ki+1) under j ↦ vertAt (r + j), and bi = edgeAt (r + k(i+1) − 1), i ∈ Fin 4; reason: consecutive intervals of a cycle are index ranges of its cyclic sequence; the orientation is the cycle's own, and the reverse orientation gives the same intervals relabeled
--   - encoding: the intersections of the four components of Fj with V(C) are exactly X1, …, X4 → every component K of (V, Fj) has {v ∈ V(C) : comp v = K} equal to some Xi, and every Xi is such a set; reason: set equality of the two families written out
--   - encoding: B1 = {b1, b3} and B2 = {b2, b4} are edge-disjoint matchings → the endpoint sets of b0, b2 are disjoint, those of b1, b3 are disjoint, and {b0, b2} ∩ {b1, b3} = ∅; reason: a matching is a set of pairwise vertex-disjoint edges (p. 6)
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), pp. 15–16, Lemma 4.2

import Mathlib
import Definitions.Def_LabelConnected_Treewidth_Multigraph
import Definitions.Def_LabelConnected_Treewidth_Witnesses

open Classical

namespace LabelConnected.Treewidth

/-- **Lemma 4.2** ([49, Corollary 1 and proof of Theorem 3]). Let `G` be an M-graph and `(C, F₁, F₂)`
an M-witness of `G`, the cycle `C = v₀ v₁ ⋯ v_{ℓ−1}` with edge `C.edgeAt k` joining `vₖ` and
`v_{k+1}` (indices mod `ℓ`). There are a starting index `r` and breakpoints
`0 = k₀ < k₁ < k₂ < k₃ < k₄ = ℓ` such that the four consecutive intervals
`Xᵢ = {v_{r+j} : kᵢ ≤ j < k_{i+1}}` (`i = 0, 1, 2, 3` for the paper's `X₁, …, X₄`, which partition
`V(C)`) satisfy:
* *Common intervals*: for each forest `F ∈ {F₁, F₂}`, the sets `K ∩ V(C)` over the components `K` of
  `F` are exactly `X₀, X₁, X₂, X₃`;
* *Alternating matchings*: with `bᵢ = C.edgeAt (r + k_{i+1} − 1)` the cycle edge joining `Xᵢ` to
  `X_{i+1}` (indices mod 4), `B₁ = {b₀, b₂}` and `B₂ = {b₁, b₃}` are edge-disjoint matchings, and
  every component of each forest contains exactly one vertex of `V(B₁)` and exactly one vertex of
  `V(B₂)`. -/
theorem lemma_4_2 {n : ℕ} {E : Type} [Fintype E] [DecidableEq E] (ends : E → Fin n × Fin n)
    (hM : IsMGraph ends) (c : Cycle ends) (F₁ F₂ : Finset E) (hW : IsMWitness ends c F₁ F₂) :
    ∃ (r : ℕ) (k : Fin 5 → ℕ) (X : Fin 4 → Finset (Fin n)) (b : Fin 4 → E),
      k 0 = 0 ∧ k 4 = c.len ∧ StrictMono k ∧
      (∀ i : Fin 4, X i = (Finset.Ico (k i.castSucc) (k i.succ)).image fun j => c.vertAt (r + j)) ∧
      (∀ i : Fin 4, b i = c.edgeAt (r + k i.succ - 1)) ∧
      -- Common intervals
      (∀ F ∈ ({F₁, F₂} : Finset (Finset E)),
        (∀ K : (adjGraph ends (F : Set E)).ConnectedComponent,
          ∃ i : Fin 4, c.vertSet.filter (fun v => compOf ends F v = K) = X i) ∧
        (∀ i : Fin 4, ∃ K : (adjGraph ends (F : Set E)).ConnectedComponent,
          c.vertSet.filter (fun v => compOf ends F v = K) = X i)) ∧
      -- Alternating matchings
      Disjoint (vertsOf ends {b 0}) (vertsOf ends {b 2}) ∧
      Disjoint (vertsOf ends {b 1}) (vertsOf ends {b 3}) ∧
      Disjoint ({b 0, b 2} : Finset E) {b 1, b 3} ∧
      (∀ F ∈ ({F₁, F₂} : Finset (Finset E)),
        ∀ K : (adjGraph ends (F : Set E)).ConnectedComponent,
          ((vertsOf ends {b 0, b 2}).filter (fun v => compOf ends F v = K)).card = 1 ∧
          ((vertsOf ends {b 1, b 3}).filter (fun v => compOf ends F v = K)).card = 1) := by sorry

end LabelConnected.Treewidth
