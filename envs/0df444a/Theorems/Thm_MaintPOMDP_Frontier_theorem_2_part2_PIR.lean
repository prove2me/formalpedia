-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_theorem_2_part2_PIR
-- name    : MaintPOMDP.Frontier.theorem_2_part2_PIR
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-24T02:04:30.901974+00:00
-- url     : https://prove2.me/theorems/e1c7e4dd-2c0f-4197-8c26-7e30965cc8c1
-- title:
--   Theorem 2(2), p. 27 — recurrent structure [PIR] when $c^I<\frac{\gamma_0}{\gamma_1}\frac1D\hat c$ (R[P] range of $c^R$)
-- statement:
--   Under the standing assumptions $0<\beta<1$, $0<c^P<c^I<c^R<c^F$, $0<\gamma_0,\gamma_1<1$, write $D=1-\beta+\beta(\gamma_0+\gamma_1)$, $\theta=(c^P+\beta\gamma_1c^F)/D$, and let $\mathbf u^{(\dot P)}=(u_0^{(\dot P)},u_1^{(\dot P)})'$, $u_F^{(\dot P)}=u_0^{(\dot P)}+c^F$ be the continuation cost of producing forever (23)–(24). Let $\hat c=(1+\beta\gamma_0)c^P-\beta\bar\gamma_1(1-\beta+\beta\gamma_0+\beta\gamma_1)c^R+\beta^2\gamma_1\bar\gamma_1c^F$ and let $g$ be the solution of the anchor equation of Lemma 7 ((40)).
--
--   **Theorem 2 (2), recurrent inspection and replacement $[PIR]$.** If $\frac{\gamma_0}{\gamma_1}\theta\le c^R<\theta$ and
--   $$c^I\ <\ \frac{\gamma_0}{\gamma_1}\frac1D\,\hat c ,$$
--   then the optimal solution of $\{P,I,R\}$ has the $[PIR]$ structure: for some minimizer $m^*$ of $g$ over $\{0,1,\dots\}$ and some indices $n_R,n_I$,
--   $$U^*=\{\mathbf u^R_0,\dots,\mathbf u^R_{n_R}\}\cup\{\mathbf u^I_0,\dots,\mathbf u^I_{n_I}\},\qquad u^*_F=g(m^*)+c^F-c^R,$$
--   where $\mathbf u^R_0=(g(m^*),g(m^*))'$, $\mathbf u^I_0$ is given by (35) with $u^R_0=g(m^*)$, and both sequences follow the production recursion (36)–(37) $\mathbf u_{i+1}=\mathbf g^P(u^*_F)+\beta\mathbf P^P\mathbf u_i$.
--
--   Here \"$(U,u_F)$ is the optimal solution of the $\{P,I,R\}$ model\" means that the dual value iteration (12)–(16) with actions $\{P,I,R\}$, started from zero terminal costs, converges to $\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ for every unnormalized belief $\boldsymbol\pi\ge0$, and its failure coordinate converges to $u_F$.
--
--   This is the $[PIR]$ row of Table 1 in the $R[P]$ range of $c^R$ (third case of Theorem 2 (2)), stated separately; as in the parent statement, the indices $n_R,n_I$ are existential and extremality of the listed points is not asserted.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), pp. 27–28, Theorem 2; p. 29, Table 1; proof EC pp. 16–20

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Theorem 2 (2), third case (p. 27; Table 1, row [PIR]): if (γ0/γ1)·thrP ≤ c^R < thrP and
c^I < (γ0/γ1)(1/D) ĉ, the {P, I, R} optimal solution has the [PIR] structure. -/
theorem theorem_2_part2_PIR (M : Params) (hM : M.Standing)
    (hlo : M.γ0 / M.γ1 * M.thrP ≤ M.cR) (hhi : M.cR < M.thrP)
    (hcI : M.cI < M.γ0 / M.γ1 * (1 / M.D) * M.chat) :
    M.PIRStructure := by sorry

end MaintPOMDP.Frontier
