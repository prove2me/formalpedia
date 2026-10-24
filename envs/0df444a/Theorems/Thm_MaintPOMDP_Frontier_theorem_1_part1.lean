-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_theorem_1_part1
-- name    : MaintPOMDP.Frontier.theorem_1_part1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T02:14:30.490441+00:00
-- url     : https://prove2.me/theorems/18c618f9-94b9-4152-96d1-95d06f672736
-- title:
--   Theorem 1(1), p. 21 — no replacement [P] under {P, R}
-- statement:
--   Under the standing assumptions $0<\beta<1$, $0<c^P<c^I<c^R<c^F$, $0<\gamma_0,\gamma_1<1$, write $\theta=(c^P+\beta\gamma_1c^F)/(1-\beta+\beta(\gamma_0+\gamma_1))$ and let $\mathbf u^{(\dot P)}$, $u_F^{(\dot P)}=u_0^{(\dot P)}+c^F$ be the continuation cost of producing forever (23)–(24).
--
--   **Theorem 1 (1), no replacement $[P]$.** If $c^R\ge\theta$, then the optimal solution of the two-action model $\{P,R\}$ is $\big(\{\mathbf u^{(\dot P)}\},\,u_F^{(\dot P)}\big)$.
--
--   Here \"$(U,u_F)$ is the optimal solution of the $\{P,R\}$ model\" means that the dual value iteration with actions $\{P,R\}$ from zero terminal costs converges to $\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ for every belief $\boldsymbol\pi\ge0$ and to $u_F$ in the failure coordinate.
--
--   This is the first conjunct of Theorem 1, stated separately.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), p. 21, Theorem 1; proof EC pp. 7–9

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Theorem 1 (1) (p. 21): if c^R ≥ thrP, the {P, R} optimal solution is ({u^(Ṗ)}, u_F^(Ṗ)). -/
theorem theorem_1_part1 (M : Params) (hM : M.Standing) (h : M.thrP ≤ M.cR) :
    M.Solves ActSet.PR {M.uPdot} M.uFPdot := by sorry

end MaintPOMDP.Frontier
