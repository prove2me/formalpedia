-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_lemma_6
-- name    : MaintPOMDP.Frontier.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:19.31826+00:00
-- url     : https://prove2.me/theorems/5719898f-f686-494b-a1df-d4bf8bea0f91
-- title:
--   Lemma 6, p. 27 — the inspection sequence u^I_i in closed form (38)–(39)
-- statement:
--   Under the standing assumptions and $\gamma_0\ne\gamma_1$, let $u^R_0\in\mathbb R$ be the anchor value and $u_F>0$. Start from the inspection point (35),
--   $$\mathbf u^I_0=\big(u^R_0-c^R+c^I,\ c^I+\beta\gamma_1u_F+\rho_1u^R_0\big)',$$
--   and set $\mathbf u^I_{i+1}=\mathbf g^P(u_F)+\beta\mathbf P^P\mathbf u^I_i$. Then for every $i\ge0$
--   $$u^I_{i,0}=\Big(\tfrac{\gamma_1}{\gamma_1-\gamma_0}c^I-c^R+\tfrac{\gamma_0}{\gamma_1-\gamma_0}\beta\gamma_1u_F+\big(1+\tfrac{\gamma_0}{\gamma_1-\gamma_0}\rho_1\big)u^R_0-\tfrac{\gamma_0}{\gamma_1-\gamma_0}\tfrac{c^P+\beta\gamma_1u_F}{\bar\rho_0}\Big)\rho_0^i-\tfrac{\gamma_0}{\gamma_1-\gamma_0}\Big(c^I+\beta\gamma_1u_F+\rho_1u^R_0-\tfrac{c^P+\beta\gamma_1u_F}{\bar\rho_1}\Big)\rho_1^i+\beta\gamma_0\tfrac{c^P+\beta\gamma_1u_F}{\bar\rho_0\bar\rho_1},$$
--   $$u^I_{i,1}=\Big(c^I+\beta\gamma_1u_F+\rho_1u^R_0-\tfrac{c^P+\beta\gamma_1u_F}{\bar\rho_1}\Big)\rho_1^i+\tfrac{c^P+\beta\gamma_1u_F}{\bar\rho_1}.$$
--
--   The inspection sequence carries the extreme points created by production after an inspection; its closed form yields the function $g$ of Lemma 7.
--
--   **Formalization Note** $\gamma_0\ne\gamma_1$ is a hypothesis because the formula divides by $\gamma_1-\gamma_0$; $u_F>0$ is kept as printed.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), p. 27, Lemma 6, (38)–(39); (35), p. 26

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Lemma 6 (p. 27): for γ0 ≠ γ1, the inspection sequence u^I_0 = (35) (with anchor u^R_0 and a
given u_F), u^I_{i+1} = g^P(u_F) + β P^P u^I_i, is given by the closed form (38)–(39). -/
theorem lemma_6 (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (uR0 uF : ℝ) (huF : 0 < uF)
    (i : ℕ) : M.prodSeq (M.inspStart uR0 uF) uF i = M.seq38_39 uR0 uF i := by sorry

end MaintPOMDP.Frontier
