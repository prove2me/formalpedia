-- Prove2me | Theorems.Thm_OffPolicyDRL_CrossFit_psi_eq_rho_add_phiEff
-- name    : OffPolicyDRL.CrossFit.psi_eq_rho_add_phiEff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:37.289985+00:00
-- url     : https://prove2.me/theorems/8c6ac676-0333-456a-a539-5e31e5e97a0b
-- title:
--   ψ(s, a, r, s′; w, q) = ρ^{πe} + φ_eff(s, a, r, s′) (p. 22)
-- statement:
--   Under the standing assumptions of the off-policy evaluation model, at the true nuisances $w'=w$, $q'=q$ the estimating function equals the estimand plus the efficient influence function: for every $(s,a,r,s')$,
--   $$\psi(s,a,r,s';w,q)=\rho^{\pi_e}+\phi_{\rm eff}(s,a,r,s'),\qquad \phi_{\rm eff}(s,a,r,s')=w(s)\eta(s,a)\big(r+\gamma v(s')-q(s,a)\big).$$
--
--   This is how $\psi$ is derived from the efficient influence function of Theorem 3. It reduces the oracle estimator $\mathbb P_n\psi(w,q)$ to $\rho^{\pi_e}$ plus an i.i.d. average of $\phi_{\rm eff}$.
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Section 4.1, display before Eq. (4), p. 22

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

theorem psi_eq_rho_add_phiEff {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace.CountablyGenerated A] (M : Model S A) (hM : M.Standing)
    (o : S × A × ℝ × S) :
    M.ψ M.w M.q o = M.ρ + M.φeff o := by sorry

end OffPolicyDRL.CrossFit
