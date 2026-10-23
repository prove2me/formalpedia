-- Prove2me | Theorems.Thm_HyperMatchDelay_Batching_reduction_4
-- name    : HyperMatchDelay.Batching.reduction_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:58.170851+00:00
-- url     : https://prove2.me/theorems/cd682f6f-db67-43f7-b91d-3be133847a3a
-- title:
--   Appendix B.3, p. 18, (3)–(4) — any subroutine satisfying condition (3) makes Randomized-Batching 1/d-competitive
-- statement:
--   Let $H = (V, E, w)$ be a shareability hypergraph with parameters $(n, d, k)$, $d, k \ge 1$, and let $\widetilde M$ be a matching of $E$ with long part $\widetilde M_\ell = \{e : \mathrm{diam}(e) > d-k\}$ and short part $\widetilde M_s = \{e : \mathrm{diam}(e) \le d-k\}$. Suppose a procedure returns, for every shift $z \in \{0,\dots,d-1\}$ and every batch index $i \in \{-1, 0, \dots, \lfloor n/d \rfloor\}$, a matching $M_{z,i}$ of the batch edges $E_{z,i}$ satisfying condition (3):
--   $$ w(M_{z,i}) \ge w(\widetilde M_\ell \cap E_{z,i}) + \frac1k\, w(\widetilde M_s \cap E_{z,i}). $$
--   Then the expected weight over a uniform shift is at least a $1/d$ fraction of $w(\widetilde M)$:
--   $$ \frac1d \sum_{z=0}^{d-1} \sum_{i} w(M_{z,i}) \;\ge\; \frac{w(\widetilde M)}{d}. $$
--
--   This is the reduction of display (4): it isolates what a batch subroutine must guarantee for Algorithm 1 to be $1/d$-competitive.
--
--   **Formalization Note** The double sum is $\mathbb E_Z[w(M)]$ for $M = \bigcup_i M_{z,i}$, since the batches are disjoint. The batch index range includes $i = -1$ (see the Model definition).
-- source:
--   Pavone, Saberi, Schiffer & Tsao, Online Hypergraph Matching with Delays, arXiv:2009.12022v1, p. 18, Appendix B.3, condition (3) and display (4)

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

/-- Appendix B.3, p. 18, condition (3) and display (4): if a procedure returns, for every shift
`z` and batch index `i`, a matching `M_{z,i}` of the batch `W_{z,i}` with
`w(M_{z,i}) ≥ w(M̃_ℓ ∩ E_{z,i}) + (1/k) w(M̃_s ∩ E_{z,i})`, then
`(1/d) ∑_z ∑_i w(M_{z,i}) ≥ w(M̃)/d`. -/
theorem reduction_4 (n d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (E : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) (hE : IsShareability n d k E w)
    (Mt : Finset (Finset ℕ)) (hMt : IsMatching E Mt)
    (Mzi : ℕ → ℤ → Finset (Finset ℕ))
    (hMzi : ∀ z ∈ Finset.range d, ∀ i ∈ batchIndices n d,
      IsMatching (batchEdges E n d z i) (Mzi z i))
    (h3 : ∀ z ∈ Finset.range d, ∀ i ∈ batchIndices n d,
      weight w (Mt.filter (fun e => (d : ℤ) - k < (diam e : ℤ)) ∩ batchEdges E n d z i) +
        (1 / (k : ℝ)) *
          weight w (Mt.filter (fun e => (diam e : ℤ) ≤ (d : ℤ) - k) ∩ batchEdges E n d z i) ≤
      weight w (Mzi z i)) :
    weight w Mt / d ≤
      (1 / (d : ℝ)) * ∑ z ∈ Finset.range d, ∑ i ∈ batchIndices n d, weight w (Mzi z i) := by sorry

end HyperMatchDelay.Batching
