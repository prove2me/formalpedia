-- Prove2me | Theorems.Thm_LabelConnected_Treewidth_lemma_5_1
-- name    : LabelConnected.Treewidth.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:29:10.938934+00:00
-- url     : https://prove2.me/theorems/d233bc39-b2f9-4247-83c3-2a76470a51a1
-- title:
--   Lemma 5.1 — the Clean-Up Rule: answer-preserving, linear time, clean with ≤ 3·C(n,2) edges, same support, labelings extend back
-- statement:
--   The Clean-Up Rule preserves whether the input is a yes-instance and can be applied exhaustively in $O(n + m)$ time. The resulting graph $G'$ is a clean spanning subgraph of $G$ with at most $3\binom{n}{2} \in O(n^2)$ edges. For every $k \ge 4$, $G$ admits an M-witness whose cycle has length at most $k$ if and only if $G'$ does. Moreover, $G'$ has the same support as $G$, and its excess and its maximum degree are at most those of $G$,
--   $$|E(G')| - (2n-4) \le |E(G)| - (2n-4),\qquad \Delta(G') \le \Delta(G).$$
--   Every temporally connecting labeling of $G'$ can be extended to one of $G$ in $O(n + m)$ time, where $m = |E(G)|$.
--
--   In the Lean statement: (i) every edge set $S$ reachable from $E(G)$ by applications of the rule gives $(V, S)$ label-connected iff $G$ is; (ii) one program outputs, in $K(n+m)+K$ steps, the edge set $S'$ of some exhaustive application; (iii) every exhaustive result $S'$ satisfies the structural clauses; (iv) one program, given $G$, an exhaustive result $S'$ and a temporally connecting labeling $\lambda'$ of $(V, S')$, outputs in $K(n+m)+K$ steps a temporally connecting labeling of $G$ that agrees with $\lambda'$ on $S'$.
--
--   Clean-Up is the universal preprocessing of the paper: afterwards $m \in O(n^2)$ and all running times are stated for clean inputs.
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
--   - encoding: the resulting graph G′, a spanning subgraph of G → G′ = restrict ends S′ = (V(G), S′) for the edge set S′ left by an exhaustive application; the algorithm outputs S′ as an index list; reason: a spanning subgraph is determined by its edge set
--   - reading: the Clean-Up Rule preserves whether the input is a yes-instance; the resulting graph G′ ("an arbitrary edge") → the equivalence for every edge set reachable by applications of the rule, and the structural clauses for every exhaustive result; reason: the deleted edge is arbitrary, so every order of application is covered
--   - encoding: maximum degree (counting parallel edges) → maxDeg: maximum over vertices of mdeg, loops counted twice; reason: degrees count multiplicities (p. 6); G′ has no loops
--   - encoding: the excess |E(G′)| − (2n − 4) → computed in ℤ; reason: avoids truncated subtraction for n ≤ 1 or few edges
--   - encoding: every temporally connecting labeling of G′ is extended (the labels are input words of the word RAM) → the labeling λ′ of G′ is given as its values in the order of the index list of S′, and in this clause every register stays within W·(1 + ⌊log₂(2 + n + m + Λ)⌋) bits, Λ the largest label of λ′; reason: a word RAM reads each input number as one word, so its words must hold the given labels; with words of Θ(log(n + m)) bits regardless of Λ the clause would be false for any λ′ with a label above 2^{W·(1+log₂(2+n+m))}
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), p. 18, Lemma 5.1

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Machine
import Definitions.Def_LabelConnected_Treewidth_Multigraph
import Definitions.Def_LabelConnected_Treewidth_Temporal
import Definitions.Def_LabelConnected_Treewidth_Witnesses
import Definitions.Def_LabelConnected_Treewidth_CleanUp
import Definitions.Def_LabelConnected_Treewidth_Encoding

open Classical

namespace LabelConnected.Treewidth

/-- **Lemma 5.1.** (i) Every application of the Clean-Up Rule preserves whether the graph is a
yes-instance of Gossiping. (ii) One deterministic word-RAM program applies the rule exhaustively in
`K·(n + m) + K` steps (output: the retained edges). (iii) Every result `G′ = (V(G), S′)` of an
exhaustive application is a clean spanning subgraph of `G` with at most `3·C(n, 2)` edges; for
every `k ≥ 4`, `G` admits an M-witness whose cycle has length at most `k` iff `G′` does; `G′` has
the same support as `G`, and its excess `|E(G′)| − (2n − 4)` and its maximum degree are at most
those of `G`. (iv) One deterministic word-RAM program extends every temporally connecting labeling
of `G′` to one of `G` in `K·(n + m) + K` steps, `m = |E(G)|`; the labels of `G′` are input words,
so in (iv) the word size is `W · (1 + log₂(2 + n + m + Λ))` with `Λ` the largest label of `G′`. -/
theorem lemma_5_1 :
    (∀ {n : ℕ} {E : Type} [Fintype E] [DecidableEq E] (ends : E → Fin n × Fin n) (S : Finset E),
      Relation.ReflTransGen (CleanUpStep ends) Finset.univ S →
        (IsLabelConnected ends ↔ IsLabelConnected (restrict ends S))) ∧
    (∃ (P : CongruencyTU.Program) (K W : ℕ), MinDegST.AddOne.Deterministic P ∧
      ∀ (n : ℕ) (es : List (Fin n × Fin n)),
        MinDegST.AddOne.WordBounded P (MinDegST.AddOne.encGraph n es) W (n + es.length) ∧
        MinDegST.AddOne.HaltsWithin P (MinDegST.AddOne.encGraph n es)
          ((K : ℝ) * ((n : ℝ) + (es.length : ℝ)) + K)
          (fun out => ∃ (S' : Finset (Fin es.length)) (l : List (Fin es.length)),
            IsCleanUpResult (ofList es) S' ∧ ListsSet l S' ∧ out = encIdx l)) ∧
    (∀ {n : ℕ} {E : Type} [Fintype E] [DecidableEq E] (ends : E → Fin n × Fin n) (S' : Finset E),
      IsCleanUpResult ends S' →
        IsClean (restrict ends S') ∧ S'.card ≤ 3 * n.choose 2 ∧
        (∀ k : ℕ, 4 ≤ k → (HasMWitnessLE ends k ↔ HasMWitnessLE (restrict ends S') k)) ∧
        support (restrict ends S') = support ends ∧
        (S'.card : ℤ) - (2 * (n : ℤ) - 4) ≤ (Fintype.card E : ℤ) - (2 * (n : ℤ) - 4) ∧
        maxDeg (restrict ends S') ≤ maxDeg ends) ∧
    (∃ (P : CongruencyTU.Program) (K W : ℕ), MinDegST.AddOne.Deterministic P ∧
      ∀ (n : ℕ) (es : List (Fin n × Fin n)) (S' : Finset (Fin es.length))
        (l : List (Fin es.length)) (lab' : Fin es.length → ℕ),
        IsCleanUpResult (ofList es) S' → ListsSet l S' →
        IsTemporalLabeling (fun e : S' => lab' e.1) →
        TemporallyConnected (restrict (ofList es) S') (fun e : S' => lab' e.1) →
        MinDegST.AddOne.WordBounded P
          (MinDegST.AddOne.encGraph n es ++ encIdx l ++ l.map fun e => (lab' e : ℤ)) W
          (n + es.length + S'.sup lab') ∧
        MinDegST.AddOne.HaltsWithin P
          (MinDegST.AddOne.encGraph n es ++ encIdx l ++ l.map fun e => (lab' e : ℤ))
          ((K : ℝ) * ((n : ℝ) + (es.length : ℝ)) + K)
          (fun out => ∃ lab : Fin es.length → ℕ, IsTemporalLabeling lab ∧
            TemporallyConnected (ofList es) lab ∧ (∀ e ∈ S', lab e = lab' e) ∧
            out = encLabels lab)) := by sorry

end LabelConnected.Treewidth
