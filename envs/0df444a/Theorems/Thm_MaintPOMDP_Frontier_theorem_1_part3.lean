-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_theorem_1_part3
-- name    : MaintPOMDP.Frontier.theorem_1_part3
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-24T02:14:37.977095+00:00
-- url     : https://prove2.me/theorems/dc1b0c73-c2a2-426f-990d-f98038dd0e6e
-- title:
--   Theorem 1(3), p. 21 — recurrent replacement [PR] under {P, R}
-- statement:
--   Under the standing assumptions $0<\beta<1$, $0<c^P<c^I<c^R<c^F$, $0<\gamma_0,\gamma_1<1$, write $\theta=(c^P+\beta\gamma_1c^F)/(1-\beta+\beta(\gamma_0+\gamma_1))$ and let $\mathbf u^{(\dot P)}$, $u_F^{(\dot P)}=u_0^{(\dot P)}+c^F$ be the continuation cost of producing forever (23)–(24). Let $f$ be the solution of the anchor equation of Lemma 3 ((31)).
--
--   **Theorem 1 (3), recurrent replacement $[PR]$.** If $c^R<\min\{\frac{\gamma_0}{\gamma_1}\theta,\theta\}$, then $f$ has a least minimizer $m^\dagger$ over $\{0,1,\dots\}$, and with $u^R=f(m^\dagger)$, $\mathbf u_0=(u^R,u^R)'$, $u^\dagger_F=u^R+c^F-c^R$ and $\mathbf u_{i+1}=\mathbf g^P(u^\dagger_F)+\beta\mathbf P^P\mathbf u_i$, the optimal solution of $\{P,R\}$ is
--   $$U^\dagger=\{\mathbf u_0,\mathbf u_1,\dots,\mathbf u_{m^\dagger+1}\},\qquad u^\dagger_F=f(m^\dagger)+c^F-c^R,$$
--   and every listed point is an extreme point of $U^\dagger$.
--
--   Here \"$(U,u_F)$ is the optimal solution of the $\{P,R\}$ model\" means that the dual value iteration with actions $\{P,R\}$ from zero terminal costs converges to $\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ for every belief $\boldsymbol\pi\ge0$ and to $u_F$ in the failure coordinate.
--
--   This is the third conjunct of Theorem 1, stated separately.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), p. 21, Theorem 1; proof EC pp. 7–9

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Theorem 1 (3) (p. 21): if c^R < min{(γ0/γ1)·thrP, thrP}, with m† the least minimizer of f
over ℕ, the {P, R} optimal solution is (U†, f(m†) + c^F − c^R) with U† = {u_0, …, u_{m†+1}}, all
extreme. -/
theorem theorem_1_part3 (M : Params) (hM : M.Standing)
    (hcR : M.cR < min (M.γ0 / M.γ1 * M.thrP) M.thrP) :
    ∃ mdag : ℕ, IsLeastMin M.f mdag ∧
      M.Solves ActSet.PR (M.Udag mdag) (M.f mdag + M.cF - M.cR) ∧
      IsExtremeSet (M.Udag mdag) := by sorry

end MaintPOMDP.Frontier
