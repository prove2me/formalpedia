-- Prove2me | Theorems.Thm_HyperMatchDelay_Batching_condition_3
-- name    : HyperMatchDelay.Batching.condition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:08.521561+00:00
-- url     : https://prove2.me/theorems/277144e1-7a6e-41cb-aa59-54a5a8514642
-- title:
--   Appendix B.3, p. 19, display (a)–(c) — Depth-k Greedy satisfies condition (3)
-- statement:
--   Let $H = (V, E, w)$ be a shareability hypergraph with parameters $(n, d, k)$, $d, k \ge 1$, and let $\sigma$ be a weight-sorted ordering oracle for Greedy. Let $\widetilde M$ be any matching of $E$, and split it into its long and short edges
--   $$ \widetilde M_\ell = \{e \in \widetilde M : \mathrm{diam}(e) > d - k\},\qquad \widetilde M_s = \{e \in \widetilde M : \mathrm{diam}(e) \le d - k\}. $$
--   For every shift $z$ and batch index $i$, the matching $M_{z,i}$ returned by Depth-k Greedy on the batch $W_{z,i} = (V_{z,i}, E_{z,i}, w)$ satisfies condition (3):
--   $$ w(M_{z,i}) \;\ge\; w(\widetilde M_\ell \cap E_{z,i}) + \frac1k\, w(\widetilde M_s \cap E_{z,i}). $$
--
--   Long edges are recovered exactly, because they form a restricted matching that Depth-k Greedy tries; short edges lose at most the Greedy factor $1/k$, which the batching later recovers.
--
--   **Formalization Note** The paper states (3) for a maximum weight matching $M^*$; the argument uses only that $M^*$ is a matching, and the statement here holds for every matching $\widetilde M$. The long/short split compares in $\mathbb Z$, so when $d < k$ all edges are long and $\widetilde M_s = \emptyset$, as in the paper.
-- source:
--   Pavone, Saberi, Schiffer & Tsao, Online Hypergraph Matching with Delays, arXiv:2009.12022v1, p. 19, Appendix B.3, display (a)–(c) establishing condition (3) of p. 18

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

/-- Appendix B.3, p. 19, display (a)–(c): Depth-k Greedy satisfies condition (3). For every
matching `M̃` of a shareability hypergraph, split into its long edges
`M̃_ℓ = {e : diam(e) > d - k}` and short edges `M̃_s = {e : diam(e) ≤ d - k}`, and every batch
`W_{z,i}`, `w(M_{z,i}) ≥ w(M̃_ℓ ∩ E_{z,i}) + (1/k) w(M̃_s ∩ E_{z,i})`. -/
theorem condition_3 (n d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (E : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) (hE : IsShareability n d k E w)
    (σ : Finset (Finset ℕ) → List (Finset ℕ)) (hσ : IsSortedOrder w σ)
    (Mt : Finset (Finset ℕ)) (hMt : IsMatching E Mt) (z : ℕ) (i : ℤ) :
    weight w (Mt.filter (fun e => (d : ℤ) - k < (diam e : ℤ)) ∩ batchEdges E n d z i) +
      (1 / (k : ℝ)) *
        weight w (Mt.filter (fun e => (diam e : ℤ) ≤ (d : ℤ) - k) ∩ batchEdges E n d z i) ≤
    weight w (depthKGreedy σ w k (window n d z i) (batchEdges E n d z i)) := by sorry

end HyperMatchDelay.Batching
