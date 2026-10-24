-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_theorem_2_part2_IRP
-- name    : MaintPOMDP.Frontier.theorem_2_part2_IRP
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T02:04:44.559998+00:00
-- url     : https://prove2.me/theorems/8f0c9ccb-6955-4adf-8d97-59b755a26bbd
-- title:
--   Theorem 2(2), p. 27 — transient inspection–replacement IR[P] under {P, I, R}
-- statement:
--   Under the standing assumptions $0<\beta<1$, $0<c^P<c^I<c^R<c^F$, $0<\gamma_0,\gamma_1<1$, write $D=1-\beta+\beta(\gamma_0+\gamma_1)$, $\theta=(c^P+\beta\gamma_1c^F)/D$, and let $\mathbf u^{(\dot P)}=(u_0^{(\dot P)},u_1^{(\dot P)})'$, $u_F^{(\dot P)}=u_0^{(\dot P)}+c^F$ be the continuation cost of producing forever (23)–(24). Let $\hat c=(1+\beta\gamma_0)c^P-\beta\bar\gamma_1(1-\beta+\beta\gamma_0+\beta\gamma_1)c^R+\beta^2\gamma_1\bar\gamma_1c^F$, $\mathbf u^{(R\dot P)}=(c^R+u_0^{(\dot P)},\,c^R+u_0^{(\dot P)})'$ and
--   $$\mathbf u^I=\big(c^I+u_0^{(\dot P)},\ c^I+\beta\bar\gamma_1(c^R+u_0^{(\dot P)})+\beta\gamma_1(c^F+u_0^{(\dot P)})\big)'.$$
--
--   **Theorem 2 (2), transient inspection and replacement $IR[P]$.** If $\frac{\gamma_0}{\gamma_1}\theta\le c^R<\theta$ and
--   $$\frac{\gamma_0}{\gamma_1}\frac1D\,\hat c\ \le\ c^I\ <\ \frac{c^R}{c^P+\beta\gamma_1c^F}\,\hat c ,$$
--   then the optimal solution of the three-action model $\{P,I,R\}$ is $\big(\{\mathbf u^{(\dot P)},\mathbf u^{(R\dot P)},\mathbf u^I\},\,u_F^{(\dot P)}\big)$.
--
--   Here \"$(U,u_F)$ is the optimal solution of the $\{P,I,R\}$ model\" means that the dual value iteration (12)–(16) with actions $\{P,I,R\}$, started from zero terminal costs, converges to $\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ for every unnormalized belief $\boldsymbol\pi\ge0$, and its failure coordinate converges to $u_F$.
--
--   This is the $IR[P]$ row of Table 1 (second case of Theorem 2 (2)), stated separately.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), pp. 27–28, Theorem 2; p. 29, Table 1; proof EC pp. 16–20

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Theorem 2 (2), second case (p. 27; Table 1, row IR[P]): if (γ0/γ1)·thrP ≤ c^R < thrP and
(γ0/γ1)(1/D) ĉ ≤ c^I < c^R ĉ / (c^P + βγ1c^F), the {P, I, R} optimal solution is
({u^(Ṗ), u^(RṖ), u^I}, u_F^(Ṗ)). -/
theorem theorem_2_part2_IRP (M : Params) (hM : M.Standing)
    (hlo : M.γ0 / M.γ1 * M.thrP ≤ M.cR) (hhi : M.cR < M.thrP)
    (hcIlo : M.γ0 / M.γ1 * (1 / M.D) * M.chat ≤ M.cI)
    (hcIhi : M.cI < M.cR / (M.cP + M.β * M.γ1 * M.cF) * M.chat) :
    M.Solves ActSet.PIR {M.uPdot, M.uRPdot, M.uIRP} M.uFPdot := by sorry

end MaintPOMDP.Frontier
