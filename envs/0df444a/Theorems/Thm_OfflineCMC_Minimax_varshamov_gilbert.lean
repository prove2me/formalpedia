-- Prove2me | Theorems.Thm_OfflineCMC_Minimax_varshamov_gilbert
-- name    : OfflineCMC.Minimax.varshamov_gilbert
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:01.882993+00:00
-- url     : https://prove2.me/theorems/a6d6fb74-0adc-497c-9f95-c48e18213f7a
-- title:
--   G.3 Part 1, p. 51 — Varshamov–Gilbert packing Σ ⊂ {−1, 1}^{d/2} with |Σ| ≥ 2^{d/16} and pairwise Hamming distance ≥ d/16
-- statement:
--   Let $d\ge2$ be even. There is a set $\Sigma\subset\{-1,1\}^{d/2}$ with
--   $$
--   |\Sigma|\ge 2^{d/16}\qquad\text{and}\qquad\sum_{i=1}^{d/2}\mathbb 1[\sigma_i\ne\sigma'_i]\ge\frac d{16}\quad\text{for all }\sigma\ne\sigma'\text{ in }\Sigma .
--   $$
--
--   This is the packing of the sign cube from which the hard subclass $\mathcal M'=\{M_\sigma:\sigma\in\Sigma\}$ of the minimax lower bound is built. Two members of $\mathcal M'$ then differ by at least $4\varepsilon$ in the $\infty$-norm.
--
--   **Formalization Note** Sign vectors are maps `Fin (d / 2) → ℤˣ`.
--
--   Differences from the source:
--   - reading: $|\Sigma|=2^{d/16}$ → $|\Sigma|\ge2^{d/16}$; reason: $2^{d/16}$ is an integer only when $16\mid d$, and when it is, a larger packing contains one of exactly that size
--   - generalization: $d>2$ even (the hypothesis of Part 1) → $d\ge2$ even; reason: covers $d=2$ as well
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, p. 51, App. G.3 Part 1 (citing Varshamov–Gilbert, [64, Theorem 5.1.7])

import Mathlib

namespace OfflineCMC.Minimax

theorem varshamov_gilbert (d : ℕ) (hd : Even d) (hd2 : 2 ≤ d) :
    ∃ S : Finset (Fin (d / 2) → ℤˣ), (2 : ℝ) ^ ((d : ℝ) / 16) ≤ (S.card : ℝ) ∧
      ∀ σ ∈ S, ∀ σ' ∈ S, σ ≠ σ' →
        (d : ℝ) / 16 ≤ ((Finset.univ.filter (fun i => σ i ≠ σ' i)).card : ℝ) := by sorry

end OfflineCMC.Minimax
