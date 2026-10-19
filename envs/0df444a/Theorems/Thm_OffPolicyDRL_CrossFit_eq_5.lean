-- Prove2me | Theorems.Thm_OffPolicyDRL_CrossFit_eq_5
-- name    : OffPolicyDRL.CrossFit.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:42.938576+00:00
-- url     : https://prove2.me/theorems/071f0c5b-2cdc-4e2f-93d5-4acb638cb4ee
-- title:
--   Eq. (5) — when q′ = q, E[ψ(w′, q)] = (1 − γ)E_{p0e}[v(s0)] = ρ^{πe} for every bounded w′
-- statement:
--   Under the standing assumptions of the off-policy evaluation model, let $(s,a,r,s')\sim p_{\pi_b}$ and let $w':S\to\mathbb R$ be bounded and measurable. Then
--   $$\mathbb E\big[\psi(s,a,r,s';w',q)\big]=(1-\gamma)\,\mathbb E_{p^{(0)}_{\pi_e}}[v(s_0)]\qquad\text{and}\qquad(1-\gamma)\,\mathbb E_{p^{(0)}_{\pi_e}}[v(s_0)]=\rho^{\pi_e}.$$
--
--   In words, the control-variate term $w'(s)\eta(s,a)\{r-q(s,a)+\gamma v(s')\}$ has mean zero for every $w'$, and the direct-method term equals the policy value. This is one half of the doubly robust (mixed-bias) structure of $\psi$.
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Eq. (5), p. 22

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

theorem eq_5 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace.CountablyGenerated A] (M : Model S A) (hM : M.Standing)
    (w' : S → ℝ) (hw' : Measurable w') (hw'b : ∃ C : ℝ, ∀ s, |w' s| ≤ C) :
    ∫ o, M.ψ w' M.q o ∂M.obsLaw = (1 - M.γ) * ∫ s, M.v s ∂M.ν0e ∧
      (1 - M.γ) * ∫ s, M.v s ∂M.ν0e = M.ρ := by sorry

end OffPolicyDRL.CrossFit
