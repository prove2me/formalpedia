-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_lemma_3
-- name    : MaintPOMDP.Frontier.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:11.096526+00:00
-- url     : https://prove2.me/theorems/2db1d997-b1fc-4b8d-8f60-4d69642aa52a
-- title:
--   Lemma 3, p. 21 — the anchor u^R solving u^R = c^R + βp_0′u_m is f(m) of (31)
-- statement:
--   Under the standing assumptions and $\gamma_0\ne\gamma_1$, fix $m\in\{0,1,\dots\}$. Suppose $u^R$ satisfies
--   $$u^R=c^R+\beta\mathbf p_0'\mathbf u_m,$$
--   where $\mathbf u_m$ is the $m$-th term of the production sequence $\mathbf u_0=(u^R,u^R)'$, $\mathbf u_{i+1}=\mathbf g^P(u_F)+\beta\mathbf P^P\mathbf u_i$ with $u_F=u^R+c^F-c^R$. Then $u^R=f(m)$, where
--   $$f(m)=\frac{\bar\rho_0\bar\rho_1c^R+\Big[\beta\gamma_0+\frac{\gamma_0}{\gamma_1-\gamma_0}\big(\bar\rho_0\rho_1^{m+1}-\bar\rho_1\rho_0^{m+1}\big)\Big]\big[c^P+\beta\gamma_1(c^F-c^R)\big]}{\bar\rho_0\bar\rho_1-\beta^2\gamma_0\gamma_1-\frac{1-\beta}{\gamma_1-\gamma_0}\big(\gamma_1\bar\rho_1\rho_0^{m+1}-\gamma_0\bar\rho_0\rho_1^{m+1}\big)} .$$
--   In particular the anchor $f(m)$ of the mission's definitions (the solution of this affine equation) equals the closed form above.
--
--   The function $f$ is the one minimized in Theorem 1: the recurrent-replacement frontier is anchored at $(f(m^\dagger),f(m^\dagger))'$.
--
--   **Formalization Note** The closed form divides by $\gamma_1-\gamma_0$, so $\gamma_0\ne\gamma_1$ is a hypothesis (footnote 2 and App. B treat $\gamma_0=\gamma_1$ separately). The second conjunct links the formula to the definition of $f$ used by the main theorems.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), p. 21, Lemma 3, (31)

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Lemma 3 (p. 21): for γ0 ≠ γ1, if u^R = c^R + β p0′u_m, where u_m is the m-th term of the
production sequence started at u_0 = (u^R, u^R)′ with u_F = u^R + c^F − c^R, then u^R = f(m) with
f the closed form (31); in particular the anchor f(m) equals (31). -/
theorem lemma_3 (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (m : ℕ) :
    (∀ uR : ℝ,
        uR = M.cR + M.β * dot M.p0 (M.prodSeq (diag uR) (uR + M.cF - M.cR) m) →
        uR = M.f31 m) ∧
      M.f m = M.f31 m := by sorry

end MaintPOMDP.Frontier
