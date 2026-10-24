-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_solves_of_bellman_fixed_point
-- name    : MaintPOMDP.Frontier.solves_of_bellman_fixed_point
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T02:04:51.384196+00:00
-- url     : https://prove2.me/theorems/1f7640ba-9ebe-4488-b74c-f507b66d4cd9
-- title:
--   Verification theorem: a Bellman fixed point $(\min_{U}\boldsymbol\pi'\mathbf u,u_F)$ is the value-iteration limit
-- statement:
--   Under the standing assumptions $0<\beta<1$, $0<c^P<c^I<c^R<c^F$, $0<\gamma_0,\gamma_1<1$, let $A$ be any of the action sets $\{P\}$, $\{P,R\}$, $\{P,I,R\}$ and let $T_A$ be one step of the dual value iteration (12)–(16) in support-function form: a pair $(W,w_F)$ is mapped to
--   $$W'(\boldsymbol\pi)=\min\Big\{\boldsymbol\pi'\mathbf g^P(w_F)+\beta W\big((\mathbf P^P)'\boldsymbol\pi\big),\ (\pi_0+\pi_1)\big(c^R+\beta W(\mathbf p_0)\big),\ \boldsymbol\pi'\mathbf g^I(w_F)+\beta\big(\pi_0W(\mathbf p_0)+\pi_1W(\mathbf p_1)\big)\Big\},\qquad w_F'=c^F+\beta W(\mathbf p_0),$$
--   keeping only the terms of the actions in $A$.
--
--   **Verification theorem.** Let $U$ be a nonempty finite set of cost vectors and $u_F\in\mathbb R$. If $W_U(\boldsymbol\pi)=\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ satisfies $T_A(W_U,u_F)_1(\boldsymbol\pi)=W_U(\boldsymbol\pi)$ for every $\boldsymbol\pi\ge0$, and $u_F=c^F+\beta W_U(\mathbf p_0)$, then value iteration from zero terminal costs converges to $(W_U,u_F)$: $W_n(\boldsymbol\pi)\to W_U(\boldsymbol\pi)$ for every $\boldsymbol\pi\ge0$ and $w_{F,n}\to u_F$.
--
--   The proof is the standard contraction argument: $T_A$ is a $\beta$-contraction for the weighted distance $\sup_{\boldsymbol\pi\ge0}|W(\boldsymbol\pi)-W'(\boldsymbol\pi)|/(\pi_0+\pi_1)$ combined with $|w_F-w_F'|$, because $(\mathbf P^P)'\boldsymbol\pi$, $\mathbf p_0$, $\mathbf p_1$ have total mass at most that of $\boldsymbol\pi$. This is the tool used to verify every candidate solution of Theorems 1 and 2 (e.g. Proposition 3 and the rows of Table 1).
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), §4.1–4.2, pp. 14–17 (dual value iteration (12)–(16) and the fixed-point characterization (18)–(22) of Proposition 2)

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Verification theorem for the dual value iteration (12)–(16): if the support function of a nonempty
finite set U together with u_F is a fixed point of the Bellman operator for the action set A (on all
beliefs π ≥ 0, and in the failure coordinate u_F = c^F + β min_U p0′u), then (U, u_F) is the optimal
solution, i.e. value iteration from zero converges to it. -/
theorem solves_of_bellman_fixed_point (M : Params) (hM : M.Standing) (A : ActSet) (U : Finset Vec)
    (hU : U.Nonempty) (uF : ℝ)
    (hfix : ∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 → (M.bellman A (minDot U, uF)).1 π = minDot U π)
    (hF : M.cF + M.β * minDot U M.p0 = uF) : M.Solves A U uF := by sorry

end MaintPOMDP.Frontier
