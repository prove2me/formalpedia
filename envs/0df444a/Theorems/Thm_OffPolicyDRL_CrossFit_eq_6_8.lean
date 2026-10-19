-- Prove2me | Theorems.Thm_OffPolicyDRL_CrossFit_eq_6_8
-- name    : OffPolicyDRL.CrossFit.eq_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:38.441067+00:00
-- url     : https://prove2.me/theorems/8c93b018-1b40-4afb-9af3-fb7d1e2ee327
-- title:
--   Eqs. (6)–(8) — when w′ = w, E[ψ(w, q′)] = ρ^{πe} for every bounded q′
-- statement:
--   Under the standing assumptions of the off-policy evaluation model, let $(s,a,r,s')\sim p_{\pi_b}$ and let $q':S\times A\to\mathbb R$ be bounded and measurable, with $v'(s)=\int q'(s,a)\,\pi_e(da\mid s)$. Then
--   $$\mathbb E\big[\psi(s,a,r,s';w,q')\big]=\mathbb E\big[w(s)\eta(s,a)r\big]+\mathbb E\big[w(s)\{-\eta(s,a)q'(s,a)+\gamma\eta(s,a)v'(s')\}\big]+(1-\gamma)\,\mathbb E_{p^{(0)}_{\pi_e}}[v'(s_0)]=\rho^{\pi_e}.$$
--
--   This is the other half of the doubly robust structure. With the true density ratio, the estimating function is unbiased whatever $q'$ is.
--
--   **Formalization Note** Only the endpoint $\mathbb E[\psi(w,q')]=\rho^{\pi_e}$ is stated. The intermediate expressions (6) and (7) of the paper are its unfolding.
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Eqs. (6)–(8), p. 23

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

theorem eq_6_8 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace.CountablyGenerated A] (M : Model S A) (hM : M.Standing)
    (q' : S × A → ℝ) (hq' : Measurable q') (hq'b : ∃ C : ℝ, ∀ x, |q' x| ≤ C) :
    ∫ o, M.ψ M.w q' o ∂M.obsLaw = M.ρ := by sorry

end OffPolicyDRL.CrossFit
