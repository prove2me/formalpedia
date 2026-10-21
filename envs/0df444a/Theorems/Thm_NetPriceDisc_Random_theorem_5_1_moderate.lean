-- Prove2me | Theorems.Thm_NetPriceDisc_Random_theorem_5_1_moderate
-- name    : NetPriceDisc.Random.theorem_5_1_moderate
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-21T00:33:56.625801+00:00
-- url     : https://prove2.me/theorems/d0f7ea2f-d2ab-405c-8d7c-b69d7c63828d
-- title:
--   Theorem 5.1, moderate-density case — E[R(p₀)] = o(n) uniformly when n·p(n) stays in [δ, M]
-- statement:
--   Fix $a>0$, a marginal cost $c<a$ and a network coefficient $\rho\in(0,1)$. For a directed network $G$ on $n$ consumers let $R(p_0)=\pi^*-\pi(p_0)$ be the regret of the uniform price $p_0=\frac{a+c}{2}\mathbf 1$, and write $\mathbb E_{n,q}$ for the expectation over the directed Erdős–Rényi network $G(n,q)$, in which each ordered pair $(i,j)$, $i\neq j$, is an arc independently with probability $q$.
--
--   For all constants $0<\delta\le M$ and every $\varepsilon>0$ there is $N$ such that for all $n\ge N$ and all $q\in[0,1]$ with $\delta\le nq\le M$,
--
--   $$
--   \mathbb E_{n,q}\big[R(p_0)\big]\le \varepsilon\, n .
--   $$
--
--   Equivalently, $\mathbb E_G[R(p_0)]=o(n)$ for every density sequence with $p(n)=\Theta(1/n)$. This is the regime of Theorem 5.1 in which the average degree $np(n)$ stays bounded away from $0$ and $\infty$. Together with the sparse regime $np(n)\to0$ and the dense regime $np(n)\to\infty$ it yields Theorem 5.1 for arbitrary density sequences.
--
--   **Formalization Note.** The statement is the uniform (in $q$) form of the $o(n)$ claim on the band $\delta\le nq\le M$; if $M<\delta$ it is vacuous. The expectation is the finite sum `erExpect` over arc sets of the Model definition.
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 12, Theorem 5.1, case p(n) = Θ(1/n) of its proof (App. D.1, pp. 36–39)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem theorem_5_1_moderate (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (δ M ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ, 0 ≤ q → q ≤ 1 → δ ≤ (n : ℝ) * q → (n : ℝ) * q ≤ M →
      erExpect n q (regret a c ρ) ≤ ε * n := by sorry

end NetPriceDisc.Random
