-- Prove2me | Theorems.Thm_HyperMatchDelay_Batching_theorem_3
-- name    : HyperMatchDelay.Batching.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:17.229988+00:00
-- url     : https://prove2.me/theorems/8f3d5bd0-a034-4c65-a8f1-ae3ce704fec5
-- title:
--   Theorem 3, p. 7 — Randomized-Batching with Depth-k Greedy is 1/d-competitive for Online-(k, d)-Max-Matching
-- statement:
--   Let $H = (V, E, w)$ be a shareability hypergraph with parameters $(n, d, k)$, $d \ge 1$, $k \ge 1$: vertices $1, \dots, n$ arrive one per time step, each hyperedge has diameter less than $d$, at most $k$ vertices and non-negative weight. Run Randomized-Batching (Algorithm 1) with Depth-k Greedy (Algorithm 2) as the offline subroutine, where Greedy breaks weight ties in an arbitrary but fixed way. Draw the shift $Z$ uniformly from $\{0, \dots, d-1\}$ and let $M_Z$ be the output. Then:
--
--   1. for every shift $z$, $M_z$ is a matching of $E$ and every edge of $M_z$ lies inside a single batch window $\{z + id, \dots, z + (i+1)d - 1\}$, so it can be committed online after all its vertices arrive and before any of them leaves;
--   2. for every matching $\widetilde M$ of $E$,
--   $$ \mathbb E_Z\big[w(M_Z)\big] = \frac1d \sum_{z=0}^{d-1} w(M_z) \;\ge\; \frac{w(\widetilde M)}{d}. $$
--
--   Taking $\widetilde M$ to be a maximum weight matching shows that the algorithm is $1/d$-competitive for Online-(k, d)-Max-Matching, the best possible ratio for $k \ge 3$ by Theorem 1 of the paper, and it is achieved by a polynomial-time algorithm for fixed $k$.
--
--   **Formalization Note** Only the competitive-ratio clause of Theorem 3 is formalized; the running-time clause $O(|E|^{k+1})$ is not. The comparison against every matching is equivalent to comparison against a maximum weight matching $M^*$. Ties in Greedy are an ordering oracle and the statement holds for every weight-sorted oracle. Hyperedges are assumed non-empty.
-- source:
--   Pavone, Saberi, Schiffer & Tsao, Online Hypergraph Matching with Delays, arXiv:2009.12022v1, p. 7, Theorem 3 (proof Appendix B.3, pp. 17–20)

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

/-- Theorem 3, p. 7 (competitive clause; proof Appendix B.3, pp. 17–20): Randomized-Batching
using Depth-k Greedy as a subroutine is `1/d`-competitive for Online-(k, d)-Max-Matching.
For every shift `z < d` the output `M_z` is a matching of `E` whose every edge lies inside one
window (online feasibility), and its expected weight over a uniform shift
`Z ∈ {0, …, d - 1}` is at least `w(M̃)/d` for every matching `M̃` of `E`. -/
theorem theorem_3 (n d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (E : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) (hE : IsShareability n d k E w)
    (σ : Finset (Finset ℕ) → List (Finset ℕ)) (hσ : IsSortedOrder w σ) :
    (∀ z < d, IsMatching E (randomizedBatching σ w n d k E z) ∧
      ∀ e ∈ randomizedBatching σ w n d k E z, ∃ i ∈ batchIndices n d, e ⊆ window n d z i) ∧
    ∀ Mt : Finset (Finset ℕ), IsMatching E Mt →
      weight w Mt / d ≤
        (1 / (d : ℝ)) * ∑ z ∈ Finset.range d,
          weight w (randomizedBatching σ w n d k E z) := by sorry

end HyperMatchDelay.Batching
