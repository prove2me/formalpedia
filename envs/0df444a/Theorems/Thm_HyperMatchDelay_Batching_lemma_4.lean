-- Prove2me | Theorems.Thm_HyperMatchDelay_Batching_lemma_4
-- name    : HyperMatchDelay.Batching.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:57.9078+00:00
-- url     : https://prove2.me/theorems/1a8d02b3-74a3-43ff-9688-e245a8a2559a
-- title:
--   Lemma 4, p. 14 — Greedy is 1/k-competitive for k-Max-Matching
-- statement:
--   Let $k \ge 1$ and let $S$ be a finite family of hyperedges, each with at most $k$ vertices and non-negative weight $w(e) \ge 0$ (a weighted hypergraph of rank at most $k$). Run Greedy (Algorithm 5): scan the edges in non-increasing order of weight, with ties broken in any way, and keep each edge that is disjoint from the edges kept so far. Then the output $G$ is a matching of $S$, and for every matching $M$ of $S$
--   $$ \frac1k\, w(M) \;\le\; w(G). $$
--
--   In particular Greedy achieves at least a $1/k$ fraction of the maximum weight matching, i.e. its competitive ratio for k-Max-Matching is at least $1/k$. This classical guarantee (also known for weighted $k$-set packing) is used inside Depth-k Greedy to handle the short edges of each batch.
--
--   **Formalization Note** The ordering with arbitrary ties is an oracle $\sigma$ satisfying the sorted-order predicate; the statement holds for every such oracle. The running-time clause of Lemma 4, $O(|E|\log|E|)$, is not formalized.
-- source:
--   Pavone, Saberi, Schiffer & Tsao, Online Hypergraph Matching with Delays, arXiv:2009.12022v1, p. 14, Lemma 4 (Algorithm 5, p. 15); cited from [6, 8]

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

/-- Lemma 4, p. 14 (competitive clause): on a rank-`k` hypergraph with non-negative weights,
Greedy (Algorithm 5, with any weight-sorted order) returns a matching whose weight is at least
`1/k` times the weight of every matching. -/
theorem lemma_4 (k : ℕ) (hk : 1 ≤ k) (w : Finset ℕ → ℝ)
    (σ : Finset (Finset ℕ) → List (Finset ℕ)) (hσ : IsSortedOrder w σ)
    (S : Finset (Finset ℕ)) (hS : ∀ e ∈ S, e.card ≤ k ∧ 0 ≤ w e) :
    IsMatching S (greedy σ S) ∧
    ∀ M, IsMatching S M → (1 / (k : ℝ)) * weight w M ≤ weight w (greedy σ S) := by sorry

end HyperMatchDelay.Batching
