-- Prove2me | Theorems.Thm_OffPolicyDRL_CrossFit_rho_eq_wEta_r
-- name    : OffPolicyDRL.CrossFit.rho_eq_wEta_r
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:29.126624+00:00
-- url     : https://prove2.me/theorems/c3879956-bc62-4a30-804b-19fae70490a0
-- title:
--   ρ^{πe} = E[w(s)η(s,a)r] — the estimand as a functional of the transition law (Sec. 2.2, after Def. 3, p. 16)
-- statement:
--   Under the standing assumptions of the off-policy evaluation model, let $(s,a,r,s')\sim p_{\pi_b}$. Then the target policy's value
--   $$\rho^{\pi_e}=\lim_{T\to\infty}\Big(\sum_{t=0}^T\gamma^t\Big)^{-1}\mathbb E_{p_{\pi_e}}\Big[\sum_{t=0}^T\gamma^tr_t\Big]$$
--   equals
--   $$\rho^{\pi_e}=\mathbb E\big[w(s)\,\eta(s,a)\,r\big],$$
--   where $w=p^{(\infty)}_{\pi_e,\gamma}/p^{(0)}_{\pi_b}$ and $\eta=\pi_e/\pi_b$.
--
--   This identifies the estimand with an expectation under the behavior data. It is the last step of Eqs. (6)–(8).
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Section 2.2, paragraph after Definition 3, p. 16

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

theorem rho_eq_wEta_r {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace.CountablyGenerated A] (M : Model S A) (hM : M.Standing) :
    M.ρ = ∫ o, M.w o.1 * M.η o.1 o.2.1 * o.2.2.1 ∂M.obsLaw := by sorry

end OffPolicyDRL.CrossFit
