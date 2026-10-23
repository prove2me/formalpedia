-- Prove2me | Theorems.Thm_HyperMatchDelay_Batching_batch_decomposition
-- name    : HyperMatchDelay.Batching.batch_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:59.611187+00:00
-- url     : https://prove2.me/theorems/1cea4998-8d8f-440f-956c-81b1acffbca4
-- title:
--   Proof of Theorem 2, p. 6 — the batches decompose the output of Randomized-Batching and w(M_z) = Σ_i w(M_{z,i})
-- statement:
--   Let $H = (V, E, w)$ be a shareability hypergraph with parameters $(n, d, k)$, $d \ge 1$, let $\sigma$ be a weight-sorted ordering oracle, and fix a shift $z \in \{0, \dots, d-1\}$. Let $V_{z,i}$ be the windows, $E_{z,i}$ the batch edges, and $M_z = \bigcup_i M_{z,i}$ the output of Randomized-Batching with subroutine Depth-k Greedy, where $M_{z,i}$ is Depth-k Greedy applied to the batch $W_{z,i} = (V_{z,i}, E_{z,i}, w)$ and $i$ ranges over $I = \{-1, 0, \dots, \lfloor n/d\rfloor\}$. Then:
--
--   1. every vertex $v \in [n]$ lies in exactly one window $V_{z,i}$ with $i \in I$;
--   2. the batch edge sets $E_{z,i}$, $i \in I$, are pairwise disjoint;
--   3. $M_z$ is a matching of $E$, and every edge of $M_z$ lies inside a single window $V_{z,i}$;
--   4. the weight decomposes over the batches:
--   $$ w(M_z) = \sum_{i \in I} w(M_{z,i}). $$
--
--   This is the bookkeeping behind the first equality of display (1) and the online feasibility of the algorithm: an edge inside $V_{z,i}$ can be committed at time $z + (i+1)d - 1$, after all its vertices have arrived and before any of them leaves.
--
--   **Formalization Note** The paper writes $i$ over $0 \le i \le n/d$; the index $-1$ is needed to cover the first $z$ vertices when $z > 0$.
-- source:
--   Pavone, Saberi, Schiffer & Tsao, Online Hypergraph Matching with Delays, arXiv:2009.12022v1, p. 6, proof of Theorem 2 (batch definition and display (1)); p. 17, Appendix B.3

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

/-- Proof of Theorem 2, p. 6, and Appendix B.3, p. 17: for every shift `z < d`, the windows
`V_{z,i}` partition `[n]`, the batches `E_{z,i}` are pairwise disjoint, the output `M_z` of
Randomized-Batching with Depth-k Greedy is a matching of `E` each of whose edges lies inside a
single window, and `w(M_z) = ∑_i w(M_{z,i})`. -/
theorem batch_decomposition (n d k : ℕ) (hd : 1 ≤ d) (E : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) (hE : IsShareability n d k E w)
    (σ : Finset (Finset ℕ) → List (Finset ℕ)) (hσ : IsSortedOrder w σ) (z : ℕ) (hz : z < d) :
    (∀ v ∈ Finset.Icc 1 n, ∃! i, i ∈ batchIndices n d ∧ v ∈ window n d z i) ∧
    ((batchIndices n d : Set ℤ).PairwiseDisjoint (fun i => batchEdges E n d z i)) ∧
    IsMatching E (randomizedBatching σ w n d k E z) ∧
    (∀ e ∈ randomizedBatching σ w n d k E z,
      ∃ i ∈ batchIndices n d, e ⊆ window n d z i) ∧
    weight w (randomizedBatching σ w n d k E z) =
      ∑ i ∈ batchIndices n d,
        weight w (depthKGreedy σ w k (window n d z i) (batchEdges E n d z i)) := by sorry

end HyperMatchDelay.Batching
