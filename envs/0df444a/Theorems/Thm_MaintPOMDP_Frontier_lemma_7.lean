-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_lemma_7
-- name    : MaintPOMDP.Frontier.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:34.856556+00:00
-- url     : https://prove2.me/theorems/23ddb247-0922-4419-9918-fdfdcf16e75e
-- title:
--   Lemma 7, p. 27 — the [PIR] anchor u^R_0 solving u^R_0 = c^R + βp_0′u^I_m is g(m) of (40)
-- statement:
--   Under the standing assumptions and $\gamma_0\ne\gamma_1$, fix $m\in\{0,1,\dots\}$. Suppose
--   $$u^R_0=c^R+\beta\mathbf p_0'\mathbf u^I_m,$$
--   where $\mathbf u^I_m$ is the $m$-th term of the inspection sequence of Lemma 6 started at (35), with $u_F=u^R_0+c^F-c^R$. Then $u^R_0=g(m)$, where
--   $$g(m)=\frac{\bar\rho_0\bar\rho_1c^R+\beta\gamma_0\big(c^P+\beta\gamma_1(c^F-c^R)\big)+a(m)}{\bar\rho_0\bar\rho_1-\beta^2\gamma_0\gamma_1+\frac{1-\beta}{\gamma_1-\gamma_0}(\gamma_0\bar\rho_0-\gamma_1)\bar\rho_1\rho_0^{m+1}+\frac{1-\beta}{\gamma_1-\gamma_0}\gamma_0\bar\rho_0\rho_1^{m+2}},$$
--   $$a(m)=-\bar\rho_0\bar\rho_1\rho_0^{m+1}c^R+\bar\rho_0\bar\rho_1\frac{\gamma_1\rho_0^{m+1}-\gamma_0\rho_1^{m+1}}{\gamma_1-\gamma_0}c^I+\frac{\gamma_0(\bar\rho_0\rho_1^{m+1}-\bar\rho_1\rho_0^{m+1})}{\gamma_1-\gamma_0}c^P+\frac{\beta\gamma_0\gamma_1(\bar\rho_0\rho_1^{m+2}-\bar\rho_1\rho_0^{m+2})}{\gamma_1-\gamma_0}(c^F-c^R).$$
--   In particular the anchor $g(m)$ of the mission's definitions equals this closed form.
--
--   The function $g$ is minimized in the recurrent-inspection structure $[PIR]$ of Theorem 2.
--
--   **Formalization Note** $\gamma_0\ne\gamma_1$ is a hypothesis because (40) divides by $\gamma_1-\gamma_0$. The second conjunct links the formula to the definition of $g$ used by the goal theorem.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), p. 27, Lemma 7, (40)

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Lemma 7 (p. 27): for γ0 ≠ γ1, if u^R_0 = c^R + β p0′u^I_m, where u^I_m is the m-th term of the
inspection sequence (35), (37) with u_F = u^R_0 + c^F − c^R, then u^R_0 = g(m) with g the closed
form (40); in particular the anchor g(m) equals (40). -/
theorem lemma_7 (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (m : ℕ) :
    (∀ uR0 : ℝ,
        uR0 = M.cR + M.β * dot M.p0
          (M.prodSeq (M.inspStart uR0 (uR0 + M.cF - M.cR)) (uR0 + M.cF - M.cR) m) →
        uR0 = M.g40 m) ∧
      M.g m = M.g40 m := by sorry

end MaintPOMDP.Frontier
