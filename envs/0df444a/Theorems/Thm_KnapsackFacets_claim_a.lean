-- Prove2me | Theorems.Thm_KnapsackFacets_claim_a
-- name    : KnapsackFacets.claim_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:58.099129+00:00
-- url     : https://prove2.me/theorems/b40dcd8f-a1df-4e9f-8171-38516c9f5f9a
-- title:
--   Theorem 4, proof, Claim A — $\sum_{i=1}^{2r}f_i>3L+2$
-- statement:
--   For every natural number $L$, with $r=\lceil\log_2(30L+20)-1\rceil$,
--   $$
--   \sum_{i=1}^{2r}f_i\ >\ 3L+2 ,
--   $$
--   where $f$ is the shifted Fibonacci sequence of (1)–(2).
--
--   In the proof of Theorem 4, $L=w([n])$; the inequality makes room in the first $2r$ coordinates for every subset sum of $w$.
--
--   Differences from the source:
--   - generalization: L = w([n]) for the CSS instance at hand → every L ∈ ℕ; reason: r depends on the instance only through L, and every value of L occurs; the paper's claim is the instance L = w([n])
--   - encoding: r = ⌈log₂(30L + 20) − 1⌉ → rOf L = Nat.clog 2 (30L + 20) − 1; reason: ⌈log₂ m − 1⌉ = ⌈log₂ m⌉ − 1 and Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1; the value is at least 4
-- source:
--   Chen & Zhu, The Complexity of Recognizing Facets for the Knapsack Polytope, arXiv:2211.03311v3, Theorem 4, proof, Claim A (first Claim), p.7; r from p.6

import Definitions.Def_KnapsackFacets_Reduction

set_option autoImplicit false

namespace KnapsackFacets

/-- **Claim A (first Claim in the proof of Theorem 4).** "Σ_{i=1}^{2r} fᵢ > 3L + 2."
Chen & Zhu, arXiv:2211.03311v3, Theorem 4, proof, Claim A, p.7, with
`r = ⌈log₂(30L + 20) − 1⌉` (p.6).

Stated for every `L ∈ ℕ`; the paper's `L = w([n])` is one instance.

**Formalization Note.** `r = rOf L = Nat.clog 2 (30L + 20) − 1`, `f = shiftedFib`. -/
theorem claim_a (L : ℕ) :
    3 * L + 2 < ∑ i ∈ Finset.Icc 1 (2 * rOf L), shiftedFib i := by sorry

end KnapsackFacets
