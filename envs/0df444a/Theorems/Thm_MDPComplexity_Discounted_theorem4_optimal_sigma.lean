-- Prove2me | Theorems.Thm_MDPComplexity_Discounted_theorem4_optimal_sigma
-- name    : MDPComplexity.Discounted.theorem4_optimal_sigma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:45:51.272247+00:00
-- url     : https://prove2.me/theorems/3e1e64ba-1b18-4534-b43a-bfb5f6bf46a5
-- title:
--   §3, discounted case, behind Theorem 4 (pp. 446–447) — optimal discounted cost = least sigma cost = min over u, k, l of λ + β^k μ/(1 − β^l) (corrected)
-- statement:
--   Let $0<\beta<1$, let $M$ be a finite deterministic stationary Markov decision process with $n$ states and initial state $s_0$, and let $J^*_\beta(s_0)=\inf_\delta\sum_{t\ge0}\beta^tc(s_t,\delta(s_t,t))$ be its optimal discounted cost, the infimum over all policies $\delta(s,t)$. Then:
--
--   1. $J^*_\beta(s_0)$ is the least discounted cost of a sigma from $s_0$, and some sigma attains it;
--   2. with $B_j=A\otimes\beta A\otimes\cdots\otimes\beta^{j-1}A$ ($B_0$ the min-plus identity),
--   $$J^*_\beta(s_0)=\min\Bigl\{\lambda+\frac{\beta^{k}\mu}{1-\beta^{l}}\;:\;u\in S,\ 0\le k\le n,\ 1\le l\le n,\ \lambda=(B_k)_{s_0u}<\infty,\ \mu=(B_l)_{uu}<\infty\Bigr\},$$
--   the minimum being attained.
--
--   This is the mathematical content of Theorem 4 of the paper ("the infinite-horizon, discounted deterministic problem is in NC"): the optimum is a minimum of polynomially many closed-form expressions in the entries of the matrix products $B_j$, each of which can be computed in parallel.
--
--   **Formalization Note** The parallel-complexity claim (membership in NC, processor and time bounds) is not formalized. The paper prints the expression as $\lambda+\beta^{k+1}\mu/(1+\beta^l)$; with $\lambda=(B_k)_{u_0u}$ covering times $0,\dots,k-1$ the cycle starts at time $k$, so we state the corrected $\lambda+\beta^k\mu/(1-\beta^l)$, and we exclude $l=0$, for which $1-\beta^0=0$. (One node with a loop of cost $1$ has optimum $1/(1-\beta)$, which the printed expression does not produce.) The paper's "$k,l=0,1,\dots,n$" uses $B_0$, which we take to be the min-plus identity. The optimum is over all time-dependent policies $\delta(s,t)$, not over stationary ones, so the first part includes the existence of a stationary optimal policy.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), pp. 446–447, §3, The infinite horizon, discounted case, and Theorem 4 (p. 447)

import Mathlib
import Definitions.Def_MDPComplexity_Discounted_Model

namespace MDPComplexity.Discounted

theorem theorem4_optimal_sigma {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S) (s₀ : S)
    (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    IsLeast {x : ℝ | ∃ P : M.Sigma s₀, x = P.cost β} (M.optDisc β s₀) ∧
    IsLeast {x : ℝ | ∃ (u : S) (k l : ℕ) (lam mu : ℝ),
        k ≤ Fintype.card S ∧ 1 ≤ l ∧ l ≤ Fintype.card S ∧
        M.B β k s₀ u = Tropical.trop (lam : WithTop ℝ) ∧
        M.B β l u u = Tropical.trop (mu : WithTop ℝ) ∧
        x = lam + β ^ k * mu / (1 - β ^ l)} (M.optDisc β s₀) := by sorry

end MDPComplexity.Discounted
