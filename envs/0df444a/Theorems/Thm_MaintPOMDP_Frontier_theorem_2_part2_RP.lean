-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_theorem_2_part2_RP
-- name    : MaintPOMDP.Frontier.theorem_2_part2_RP
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T02:04:43.305508+00:00
-- url     : https://prove2.me/theorems/0038d385-122f-462c-898d-cbe5b12643e2
-- title:
--   Theorem 2(2), p. 27 — transient replacement R[P] under {P, I, R}
-- statement:
--   Under the standing assumptions $0<\beta<1$, $0<c^P<c^I<c^R<c^F$, $0<\gamma_0,\gamma_1<1$, write $D=1-\beta+\beta(\gamma_0+\gamma_1)$, $\theta=(c^P+\beta\gamma_1c^F)/D$, and let $\mathbf u^{(\dot P)}=(u_0^{(\dot P)},u_1^{(\dot P)})'$, $u_F^{(\dot P)}=u_0^{(\dot P)}+c^F$ be the continuation cost of producing forever (23)–(24). Let
--   $$\hat c=(1+\beta\gamma_0)c^P-\beta\bar\gamma_1(1-\beta+\beta\gamma_0+\beta\gamma_1)c^R+\beta^2\gamma_1\bar\gamma_1c^F$$
--   and $\mathbf u^{(R\dot P)}=(c^R+u_0^{(\dot P)},\,c^R+u_0^{(\dot P)})'$.
--
--   **Theorem 2 (2), transient replacement $R[P]$.** If $\frac{\gamma_0}{\gamma_1}\theta\le c^R<\theta$ and
--   $$c^I\ \ge\ \frac{c^R}{c^P+\beta\gamma_1c^F}\,\hat c ,$$
--   then the optimal solution of the three-action model $\{P,I,R\}$ is $\big(\{\mathbf u^{(\dot P)},\mathbf u^{(R\dot P)}\},\,u_F^{(\dot P)}\big)$: inspection is never used.
--
--   Here \"$(U,u_F)$ is the optimal solution of the $\{P,I,R\}$ model\" means that the dual value iteration (12)–(16) with actions $\{P,I,R\}$, started from zero terminal costs, converges to $\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ for every unnormalized belief $\boldsymbol\pi\ge0$, and its failure coordinate converges to $u_F$.
--
--   This is the $R[P]$ row of Table 1 (first case of Theorem 2 (2)), stated separately.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), pp. 27–28, Theorem 2; p. 29, Table 1; proof EC pp. 16–20

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Theorem 2 (2), first case (p. 27; Table 1, row R[P]): if (γ0/γ1)·thrP ≤ c^R < thrP and
c^I ≥ c^R ĉ / (c^P + βγ1c^F), the {P, I, R} optimal solution is ({u^(Ṗ), u^(RṖ)}, u_F^(Ṗ)). -/
theorem theorem_2_part2_RP (M : Params) (hM : M.Standing)
    (hlo : M.γ0 / M.γ1 * M.thrP ≤ M.cR) (hhi : M.cR < M.thrP)
    (hcI : M.cR / (M.cP + M.β * M.γ1 * M.cF) * M.chat ≤ M.cI) :
    M.Solves ActSet.PIR {M.uPdot, M.uRPdot} M.uFPdot := by sorry

end MaintPOMDP.Frontier
