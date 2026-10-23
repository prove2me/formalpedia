-- Prove2me | Theorems.Thm_KWPurify_Rate_eq_14_multiplicities
-- name    : KWPurify.Rate.eq_14_multiplicities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:45.800165+00:00
-- url     : https://prove2.me/theorems/d1c3efbb-884f-47a5-9668-2e9ce549cd24
-- title:
--   p. 9 — generating identity for $\dim\mathcal K_{N,s}$; the weights $w_N(s)$ form a probability vector
-- statement:
--   Fix $N \in \mathbb N$ and write the spins $s \in I[N]$ as $s = N/2 - k$ with $k = 0,\dots,\lfloor N/2\rfloor$. Let $m(N,k) = \dfrac{N-2k+1}{N-k+1}\dbinom{N}{k}$ be the multiplicity $\dim\mathcal K_{N,s}$.
--
--   1. For every real $\beta$,
--   $$\sinh(\beta)\,(2\cosh\beta)^N = \sum_{k=0}^{\lfloor N/2\rfloor} \sinh\big((N-2k+1)\beta\big)\, m(N,k),$$
--   i.e. $\sinh(\beta)(2\cosh\beta)^N = \sum_{s\in I[N]}\sinh((2s+1)\beta)\dim\mathcal K_{N,s}$.
--   2. For every $\beta > 0$ the weights $w_N(s)$ of eq. (14) satisfy $0 \le w_N(s) \le 1$ and $\sum_{s\in I[N]} w_N(s) = 1$.
--
--   The identity is the generating functional from which the paper reads off the multiplicities; the second part says that $s \mapsto w_N(s)$ is a probability distribution on the spins, which is how Lemma 6.1 uses it.
-- source:
--   Keyl & Werner, The Rate of Optimal Purification procedures, arXiv:quant-ph/9910124v1, p. 8 (after eq. (14): Σ_s w_N(s) = 1, 0 ≤ w_N(s) ≤ 1) and p. 9, §3.3 (generating functional, formula for dim K_{N,s})

import Mathlib
import Definitions.Def_KWPurify_Rate_Blocks

namespace KWPurify.Rate
theorem eq_14_multiplicities (N : ℕ) :
    (∀ β : ℝ, Real.sinh β * (2 * Real.cosh β) ^ N =
      ∑ k ∈ Finset.range (N / 2 + 1),
        Real.sinh (((N - 2 * k : ℕ) + 1 : ℝ) * β) * spinMult N k) ∧
    (∀ β : ℝ, 0 < β →
      (∀ k ∈ Finset.range (N / 2 + 1), 0 ≤ spinWeight β N k ∧ spinWeight β N k ≤ 1) ∧
      ∑ k ∈ Finset.range (N / 2 + 1), spinWeight β N k = 1) := by sorry
end KWPurify.Rate
