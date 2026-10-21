-- Prove2me | Theorems.Thm_NetPriceDisc_Random_theorem_5_1_dense
-- name    : NetPriceDisc.Random.theorem_5_1_dense
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-21T00:33:49.903678+00:00
-- url     : https://prove2.me/theorems/682abac4-b7c2-46a8-afad-c1f13f5a4f8c
-- title:
--   Theorem 5.1, dense case — E[R(p₀)] = o(n) uniformly when n·p(n) → ∞
-- statement:
--   Fix $a>0$, a marginal cost $c<a$ and a network coefficient $\rho\in(0,1)$. For a directed network $G$ on $n$ consumers let $R(p_0)=\pi^*-\pi(p_0)$ be the regret of the uniform price $p_0=\frac{a+c}{2}\mathbf 1$, and write $\mathbb E_{n,q}$ for the expectation over the directed Erdős–Rényi network $G(n,q)$, in which each ordered pair $(i,j)$, $i\neq j$, is an arc independently with probability $q$.
--
--   For every $\varepsilon>0$ there are $M$ and $N$ such that for all $n\ge N$ and all $q\in[0,1]$ with $nq\ge M$,
--
--   $$
--   \mathbb E_{n,q}\big[R(p_0)\big]\le \varepsilon\, n .
--   $$
--
--   Equivalently, $\mathbb E_G[R(p_0)]=o(n)$ for every density sequence with $n\,p(n)\to\infty$. This is the dense regime of Theorem 5.1, in which the average degree $np(n)$ diverges. Together with the sparse regime $np(n)\to0$ and the moderate regime $p(n)=\Theta(1/n)$ it yields Theorem 5.1 for arbitrary density sequences.
--
--   **Formalization Note.** The statement is the uniform (in $q$) form of the $o(n)$ claim for $np(n)\to\infty$, which is equivalent to the sequence form. The expectation is the finite sum `erExpect` over arc sets of the Model definition.
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 12, Theorem 5.1, case n·p(n) → ∞ of its proof (App. D.1, pp. 36–39)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem theorem_5_1_dense (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ, 0 ≤ q → q ≤ 1 → M ≤ (n : ℝ) * q →
      erExpect n q (regret a c ρ) ≤ ε * n := by sorry

end NetPriceDisc.Random
