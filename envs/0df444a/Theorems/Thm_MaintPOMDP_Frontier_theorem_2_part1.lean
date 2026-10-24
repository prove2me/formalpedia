-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_theorem_2_part1
-- name    : MaintPOMDP.Frontier.theorem_2_part1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T02:04:50.395109+00:00
-- url     : https://prove2.me/theorems/59bda00e-90c3-425e-98b7-51840893422b
-- title:
--   Theorem 2(1), p. 27 — no replacement [P]: if $c^R\ge\theta$, the {P, I, R} optimal solution is $(\{\mathbf u^{(\dot P)}\},u_F^{(\dot P)})$
-- statement:
--   Under the standing assumptions $0<\beta<1$, $0<c^P<c^I<c^R<c^F$, $0<\gamma_0,\gamma_1<1$, write $D=1-\beta+\beta(\gamma_0+\gamma_1)$, $\theta=(c^P+\beta\gamma_1c^F)/D$, and let $\mathbf u^{(\dot P)}=(u_0^{(\dot P)},u_1^{(\dot P)})'$, $u_F^{(\dot P)}=u_0^{(\dot P)}+c^F$ be the continuation cost of producing forever (23)–(24).
--
--   **Theorem 2 (1), no replacement $[P]$.** If $c^R\ge\theta$, then the optimal solution of the three-action model $\{P,I,R\}$ is
--   $$(U^*,u^*_F)=\big(\{\mathbf u^{(\dot P)}\},\,u_F^{(\dot P)}\big),$$
--   i.e. it is optimal never to inspect or replace preventively.
--
--   Here \"$(U,u_F)$ is the optimal solution of the $\{P,I,R\}$ model\" means that the dual value iteration (12)–(16) with actions $\{P,I,R\}$, started from zero terminal costs, converges to $\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ for every unnormalized belief $\boldsymbol\pi\ge0$, and its failure coordinate converges to $u_F$.
--
--   This is the first conjunct of Theorem 2 (the $[P]$ row of Table 1), stated separately.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), pp. 27–28, Theorem 2; p. 29, Table 1; proof EC pp. 16–20

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Theorem 2 (1) (p. 27; Table 1, row [P]): if c^R ≥ thrP, the {P, I, R} optimal solution is
({u^(Ṗ)}, u_F^(Ṗ)). -/
theorem theorem_2_part1 (M : Params) (hM : M.Standing) (h : M.thrP ≤ M.cR) :
    M.Solves ActSet.PIR {M.uPdot} M.uFPdot := by sorry

end MaintPOMDP.Frontier
