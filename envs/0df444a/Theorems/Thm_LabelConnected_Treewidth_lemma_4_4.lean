-- Prove2me | Theorems.Thm_LabelConnected_Treewidth_lemma_4_4
-- name    : LabelConnected.Treewidth.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:29:00.316676+00:00
-- url     : https://prove2.me/theorems/f7363911-e06b-48a9-9914-f93dd34a3b66
-- title:
--   Lemma 4.4 — a temporally connecting labeling from a T-witness or an M-witness in O(n + m) time
-- statement:
--   Given a T-witness or an M-witness of $G$, a temporal labeling under which $G$ is temporally connected can be constructed in $O(n + m)$ time. In the Lean statement: one deterministic word-RAM program and constants $K, W$, fixed before the input, such that for every multigraph $G$ (vertices $0..n-1$, $m$ edges) and every T-witness $(T_1, T_2)$ of $G$ (input: $G$, tag $0$, $T_1$, $T_2$) and every M-witness $(C, F_1, F_2)$ of $G$ (input: $G$, tag $1$, $E(C)$, $F_1$, $F_2$), registers stay within $W(1 + \log_2(2+n+m))$ bits and the program halts within
--   $$K\,(n + m) + K$$
--   steps with output $[\lambda(e_1), \dots, \lambda(e_m)]$, every $\lambda(e_i) \ge 1$, and $(G, \lambda)$ temporally connected.
--
--   This is the step that turns recognition into construction: every algorithm of the paper that finds a witness outputs a labeling within the same time.
--
--   Differences from the source:
--
--   - encoding: an undirected multigraph G = (V, E), parallel edges distinct, loops allowed → vertices Fin n, a finite edge type E and an endpoint map ends : E → Fin n × Fin n (a loop is an edge with equal endpoints, parallel edges are distinct edges with the same unordered endpoint pair); reason: Lean convention; every finite multigraph is one of these up to renaming
--   - encoding: (V, F) connected; a spanning tree / spanning forest of G → adjGraph ends F is Preconnected (the vertex-free graph counts as connected); a spanning tree is an edge set T with (V, T) a connected forest, a spanning forest an edge set with no cycle; reason: connectivity ignores loops and multiplicities; the only instance affected is n = 0, where every clause involved holds trivially
--   - encoding: a cycle v0e1v1···eℓvℓ of G, identified with its subgraph → a Cycle ends: length len ≥ 1, injective vertex map vert : Fin len → Fin n, injective edge map edge : Fin len → E, edge i joining vert i and vert (i + 1 mod len); E(C) and V(C) are the images; reason: the paper's own definition (p. 6) as a cyclic sequence
--   - encoding: λ: E → N assigning one positive integer to each edge → lab : E → ℕ with 0 < lab e for every edge e; reason: ℕ contains 0 in Lean
--   - encoding: a strict temporal path traversing edges e1, …, eℓ with λ(e1) < ··· < λ(eℓ), paths without repeated vertices, length 0 allowed → ℓ ∈ ℕ, an injective vertex sequence v : Fin (ℓ+1) → Fin n from u to w, edges e i joining v i and v (i+1), labels strictly increasing; reason: the paper's path convention (p. 6) written out
--   - encoding: computed in O(n + m) time on the word RAM with Θ(log(n+m))-bit words → one deterministic program of the published integer RAM CongruencyTU (no coin, no query) and constants fixed before the input; every register at every step within W·(1 + ⌊log₂(2 + n + m)⌋) bits; halting within K·(n + m) + K steps; reason: O(·) as explicit universal constants on one fixed machine; the word bound keeps unit-cost arithmetic honest
--   - encoding: the input multigraph (and edge sets / witnesses handed to the algorithm) → [n, m, u1, v1, …, um, vm] (MinDegST.AddOne.encGraph), edge e_i referred to by its index i − 1, an edge set as its length followed by its indices, each once, in any order; reason: a running time needs a fixed input representation; the edge-list representation is the paper's (p. 18, proof of Lemma 5.1)
--   - encoding: given a T-witness or an M-witness of G → one program for both kinds, told which by a tag 0 / 1 after the graph; the cycle given by its edge set in any order; reason: the input must say which witness it carries; the cyclic order of C is recoverable from E(C) in linear time and is not assumed
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), p. 17, Lemma 4.4 (implementation pp. 62–63)

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Machine
import Definitions.Def_LabelConnected_Treewidth_Multigraph
import Definitions.Def_LabelConnected_Treewidth_Witnesses
import Definitions.Def_LabelConnected_Treewidth_Encoding

open Classical

namespace LabelConnected.Treewidth

/-- **Lemma 4.4** (linear-time implementation of the classical construction). One deterministic
word-RAM program and constants `K, W`, fixed before the input: given a multigraph `G` with a
T-witness `(T₁, T₂)` (input tag `0`) or with an M-witness `(C, F₁, F₂)` (input tag `1`, the cycle
given by its edge set), registers stay within `W · (1 + log₂(2 + n + m))` bits and the program halts
within `K·(n + m) + K` steps with output `[λ(e₁), …, λ(e_m)]`, a temporal labeling under which `G` is
temporally connected. -/
theorem lemma_4_4 :
    ∃ (P : CongruencyTU.Program) (K W : ℕ), MinDegST.AddOne.Deterministic P ∧
      (∀ (n : ℕ) (es : List (Fin n × Fin n)) (T₁ T₂ : Finset (Fin es.length))
          (l₁ l₂ : List (Fin es.length)),
        IsTWitness (ofList es) T₁ T₂ → ListsSet l₁ T₁ → ListsSet l₂ T₂ →
        MinDegST.AddOne.WordBounded P (encTWitnessInput n es l₁ l₂) W (n + es.length) ∧
        MinDegST.AddOne.HaltsWithin P (encTWitnessInput n es l₁ l₂)
          ((K : ℝ) * ((n : ℝ) + (es.length : ℝ)) + K) (IsConnectingLabelingOutput es)) ∧
      (∀ (n : ℕ) (es : List (Fin n × Fin n)) (c : Cycle (ofList es))
          (F₁ F₂ : Finset (Fin es.length)) (lC l₁ l₂ : List (Fin es.length)),
        IsMWitness (ofList es) c F₁ F₂ → ListsSet lC c.edgeSet → ListsSet l₁ F₁ →
        ListsSet l₂ F₂ →
        MinDegST.AddOne.WordBounded P (encMWitnessInput n es lC l₁ l₂) W (n + es.length) ∧
        MinDegST.AddOne.HaltsWithin P (encMWitnessInput n es lC l₁ l₂)
          ((K : ℝ) * ((n : ℝ) + (es.length : ℝ)) + K) (IsConnectingLabelingOutput es)) := by sorry

end LabelConnected.Treewidth
