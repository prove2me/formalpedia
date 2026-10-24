-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_theorem_1_part2
-- name    : MaintPOMDP.Frontier.theorem_1_part2
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T02:14:35.851422+00:00
-- url     : https://prove2.me/theorems/f63d514a-92a8-4138-aa4f-63a7fbc953e6
-- title:
--   Theorem 1(2), p. 21 — transient replacement R[P] under {P, R}
-- statement:
--   Under the standing assumptions $0<\beta<1$, $0<c^P<c^I<c^R<c^F$, $0<\gamma_0,\gamma_1<1$, write $\theta=(c^P+\beta\gamma_1c^F)/(1-\beta+\beta(\gamma_0+\gamma_1))$ and let $\mathbf u^{(\dot P)}$, $u_F^{(\dot P)}=u_0^{(\dot P)}+c^F$ be the continuation cost of producing forever (23)–(24). Let $\mathbf u^{(R\dot P)}=(c^R+u_0^{(\dot P)},\,c^R+u_0^{(\dot P)})'$.
--
--   **Theorem 1 (2), transient replacement $R[P]$.** If $\frac{\gamma_0}{\gamma_1}\theta\le c^R<\theta$, then the optimal solution of the two-action model $\{P,R\}$ is $\big(\{\mathbf u^{(\dot P)},\mathbf u^{(R\dot P)}\},\,u_F^{(\dot P)}\big)$, and both points are extreme points of this set (each is the strict unique minimizer of $\boldsymbol\pi'\cdot$ over the set for some $\boldsymbol\pi$ in the closed simplex).
--
--   Here \"$(U,u_F)$ is the optimal solution of the $\{P,R\}$ model\" means that the dual value iteration with actions $\{P,R\}$ from zero terminal costs converges to $\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ for every belief $\boldsymbol\pi\ge0$ and to $u_F$ in the failure coordinate.
--
--   This is the second conjunct of Theorem 1, stated separately.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), p. 21, Theorem 1; proof EC pp. 7–9

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Theorem 1 (2) (p. 21): if (γ0/γ1)·thrP ≤ c^R < thrP, the {P, R} optimal solution is
({u^(Ṗ), u^(RṖ)}, u_F^(Ṗ)), and both points are extreme. -/
theorem theorem_1_part2 (M : Params) (hM : M.Standing)
    (hlo : M.γ0 / M.γ1 * M.thrP ≤ M.cR) (hhi : M.cR < M.thrP) :
    M.Solves ActSet.PR {M.uPdot, M.uRPdot} M.uFPdot ∧ IsExtremeSet {M.uPdot, M.uRPdot} := by sorry

end MaintPOMDP.Frontier
