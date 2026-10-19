-- Prove2me | Theorems.Thm_GreenTao_bounded_model_of_mixed_estimates
-- name    : GreenTao.bounded_model_of_mixed_estimates
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T20:54:02.544572+00:00
-- url     : https://prove2.me/theorems/207767b0-81ee-4978-9525-7ecd5e70928e
-- title:
--   Bounded model from a structured part and mixed-progression estimates
-- statement:
--   Let $k\ge0$, let $G=\mathbb Z/m\mathbb Z$ for a positive integer $m$, and let $f,s,u:G\to\mathbb R$. Suppose $\varepsilon,\xi\ge0$ and
--
--   $$0\le s\le1+\varepsilon,\qquad 0\le s+u\le f,\qquad\mathbb E s\ge\mathbb E f-\varepsilon.$$
--
--   For every nonempty subset $S\subseteq\{0,\ldots,k-1\}$, let $F^S_j=u$ when $j\in S$ and $F^S_j=s$ otherwise. Assume
--
--   $$\left|T_k(F^S_0,\ldots,F^S_{k-1})\right|\le\xi\qquad(S\ne\varnothing),$$
--
--   where $T_k$ is the multilinear progression average. Then there exists $g:G\to[0,1]$ such that
--
--   $$\mathbb E g\ge\mathbb E f-2\varepsilon,\qquad T_k(g)\le T_k(f)+2^k\xi.$$
--
--   The count includes zero common differences. This finite implication isolates the normalization and multilinearity step in passing from a structured decomposition to a bounded model. It needs no pseudorandomness assumption, no primality assumption, and no asymptotic limit.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §8 proof of Theorem 3.5 assuming Proposition 8.1: the mixed-progression expansion and monotonicity for the truncated function, together with footnote 16 for normalization to [0,1]. This auxiliary finite formulation makes the elementary errors 2ε and 2^k ξ explicit; it is not a verbatim numbered theorem.

import Definitions.Def_GreenTao_Uniformity
open scoped BigOperators
open GreenTao

theorem GreenTao.bounded_model_of_mixed_estimates (k : ℕ) (m : ℕ+) (f s u : ZMod (m : ℕ) → ℝ)
    (ε ξ : ℝ) (hε : 0 ≤ ε) (hξ : 0 ≤ ξ)
    (hs : ∀ x, 0 ≤ s x ∧ s x ≤ 1 + ε)
    (htu : ∀ x, 0 ≤ s x + u x ∧ s x + u x ≤ f x)
    (hmean : avg f - ε ≤ avg s)
    (hmixed : ∀ S : Finset (Fin k), S.Nonempty →
      |mixedAPAvg k (fun j x => if j ∈ S then u x else s x)| ≤ ξ) :
    ∃ g : ZMod (m : ℕ) → ℝ,
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      avg f - 2 * ε ≤ avg g ∧
      apAvg k g - (2 : ℝ) ^ k * ξ ≤ apAvg k f := by sorry
