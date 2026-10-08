-- Prove2me | Theorems.Thm_MDPComplexity_Discounted_sigma_cost_closed_form
-- name    : MDPComplexity.Discounted.sigma_cost_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:45:43.578684+00:00
-- url     : https://prove2.me/theorems/06b2f5aa-6776-46b6-b65d-104ab752f3d0
-- title:
--   §3, discounted case (p. 446) — the discounted cost of a sigma in closed form (indices corrected)
-- statement:
--   Let $0<\beta<1$ and let $P$ be a sigma from $s_0$ in a deterministic Markov decision process: a walk $w_0=s_0,\dots,w_N$ along decisions $e_0,\dots,e_{N-1}$ with distinct nodes $w_0,\dots,w_{N-1}$ and $w_N=w_j$ for some $j<N$. Write $c_t=c(w_t,e_t)$ for the cost of its $t$-th arc and $l=N-j\ge 1$ for the length of its cycle. Then the discounted cost of the infinite walk that follows $P$ and repeats the cycle forever is
--
--   $$c(P)=\sum_{t=0}^{j-1}\beta^t c_t+\frac{\beta^{j}}{1-\beta^{l}}\sum_{t=0}^{l-1}\beta^{t}c_{j+t}.$$
--
--   This is the formula the paper uses to evaluate a sigma; it turns the infinite discounted sum into a finite expression in the prefix cost and the cycle cost.
--
--   **Formalization Note** The paper prints $c(P)=\sum_{i=0}^{k}c(u_j,u_{j+1})\beta^i+\frac{\beta^{k+1}}{1-\beta^l}\sum_{j=1}^{l}c(v_i,v_{i+1 \bmod l})\beta^j$, with mixed summation indices and a factor $\beta^j$ in the cycle sum that is one power of $\beta$ too many for the sentence that follows it ("the discounted cost of a sigma coincides with the discounted cost of an infinite path that follows the sigma and repeats the cycle forever"). We state the corrected identity, which agrees with that sentence: with the paper's $j=k+1$, the cycle's $t$-th arc ($t=0,\dots,l-1$) carries $\beta^{t}$, i.e. the paper's $\beta^{j-1}$ for $j=1,\dots,l$, and $u_{k+1}=v_1$. The left side is the definition of the sigma's cost (an infinite series); $0<\beta<1$ is the paper's $\beta\in(0,1)$.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 446, §3, The infinite horizon, discounted case (display defining c(P) and the sentence after it)

import Mathlib
import Definitions.Def_MDPComplexity_Discounted_Model

namespace MDPComplexity.Discounted

open Finset

theorem sigma_cost_closed_form {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S) (s₀ : S)
    (P : M.Sigma s₀) (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    P.cost β = ∑ t ∈ range P.j, β ^ t * P.arcCost t +
      β ^ P.j / (1 - β ^ (P.N - P.j)) * ∑ t ∈ range (P.N - P.j), β ^ t * P.arcCost (P.j + t) := by sorry

end MDPComplexity.Discounted
