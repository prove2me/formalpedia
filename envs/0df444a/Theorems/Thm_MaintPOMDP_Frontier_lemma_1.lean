-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_lemma_1
-- name    : MaintPOMDP.Frontier.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:13.500344+00:00
-- url     : https://prove2.me/theorems/f629db82-0716-4482-b935-192eacfd401f
-- title:
--   Lemma 1, p. 19 — the production sequence u_{i+1} = g^P(u_F) + βP^P u_i in closed form (29)–(30)
-- statement:
--   Under the standing assumptions and $\gamma_0\ne\gamma_1$, let $u^R\in\mathbb R$ and $u_F>0$, and define $\mathbf u_0=(u^R,u^R)'$ and $\mathbf u_{i+1}=\mathbf g^P(u_F)+\beta\mathbf P^P\mathbf u_i$. With $\bar\gamma_x=1-\gamma_x$, $\rho_x=\beta\bar\gamma_x$, $\bar\rho_x=1-\rho_x$, for every $i\ge0$,
--   $$u_{i,0}=\frac{\gamma_1}{\gamma_1-\gamma_0}\Big(u^R-\frac{\gamma_0}{\gamma_1}\frac{c^P+\beta\gamma_1u_F}{\bar\rho_0}\Big)\rho_0^i-\frac{\gamma_0}{\gamma_1-\gamma_0}\Big(u^R-\frac{c^P+\beta\gamma_1u_F}{\bar\rho_1}\Big)\rho_1^i+\frac{\beta\gamma_0(c^P+\beta\gamma_1u_F)}{\bar\rho_0\bar\rho_1},$$
--   $$u_{i,1}=\Big(u^R-\frac{c^P+\beta\gamma_1u_F}{\bar\rho_1}\Big)\rho_1^i+\frac{c^P+\beta\gamma_1u_F}{\bar\rho_1}.$$
--
--   The production sequence carries the extreme points of the frontier created by action $P$; the closed form is what turns the anchor equation of Lemma 3 into the explicit function $f$.
--
--   **Formalization Note** The paper writes the formula without the hypothesis $\gamma_0\ne\gamma_1$ and reads it by L'Hôpital's rule at $\gamma_0=\gamma_1$ (footnote 2); here $\gamma_0\ne\gamma_1$ is a hypothesis, since Lean's division by zero returns 0. The hypothesis $u_F>0$ is kept as printed.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), p. 19, Lemma 1, (29)–(30)

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Lemma 1 (p. 19): for γ0 ≠ γ1, the production sequence u_0 = (u^R, u^R)′,
u_{i+1} = g^P(u_F) + β P^P u_i is given by the closed form (29)–(30). -/
theorem lemma_1 (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (uR uF : ℝ) (huF : 0 < uF)
    (i : ℕ) : M.prodSeq (diag uR) uF i = M.seq29_30 uR uF i := by sorry

end MaintPOMDP.Frontier
