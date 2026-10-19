-- Prove2me | Theorems.Thm_OffPolicyDRL_CrossFit_term_30_bound
-- name    : OffPolicyDRL.CrossFit.term_30_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:43.56171+00:00
-- url     : https://prove2.me/theorems/492eca61-8c14-436e-90cf-513300a8a054
-- title:
--   Proof of Thm 6, Term (30), corrected constant: |E[ψ(ŵ, q̂)] − ρ^{πe}| ≤ C_η(1 + γ√(C_{S′}C_η))‖ŵ − w‖₂‖q̂ − q‖₂
-- statement:
--   Under the standing assumptions of the off-policy evaluation model, suppose there are constants $C_w,C_{S'},C_\eta>0$ such that:
--
--   1. $w\le C_w$ almost surely under $p^{(0)}_{\pi_b}$;
--   2. the law of $s'$ in the data is at most $C_{S'}\,p^{(0)}_{\pi_b}$;
--   3. $\eta\le C_\eta$ almost surely under $p^{(0)}_{\pi_b}\otimes\pi_b$.
--
--   Let $\hat w$ and $\hat q$ be measurable with $0\le\hat w\le C_w$ and $0\le\hat q\le(1-\gamma)^{-1}R_{\max}$. Then, with $(s,a,r,s')\sim p_{\pi_b}$,
--   $$\Big|\mathbb E\big[\psi(s,a,r,s';\hat w,\hat q)\big]-\rho^{\pi_e}\Big|\le\Big(C_\eta+\gamma C_\eta\sqrt{C_{S'}C_\eta}\Big)\,\|\hat w-w\|_2\,\|\hat q-q\|_2 .$$
--
--   This is the mixed-bias property behind Term (30). The bias of the plug-in estimating function is second order: it is a product of the two nuisance errors. With cross-fitting, $\hat w,\hat q$ are the opposite fold's estimates, and the bound turns the rate condition $\kappa^w_n\kappa^q_n=o_p(n^{-1/2})$ into $\sqrt n\cdot$bias $=o_p(1)$.
--
--   The paper's display bounds the bias by $\|\hat w-w\|_2\|\eta\|_2\|\hat q-q\|_2$ and $\sqrt{\gamma C'_S}\|\hat w-w\|_2\|\eta\|_2\|\hat q-q\|_2$. A product of three $L^2$ norms does not bound the expectation of a triple product, so this is replaced by the sup bound $C_\eta$ on $\eta$ and the corrected Jensen step. **Corrected** (constant; bounded $\eta$ added).
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Appendix C, Proof of Theorems 6 and 7, "Term (30) is op(1)", p. 60 (corrected constant)

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

theorem term_30_bound {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace.CountablyGenerated A] (M : Model S A) (hM : M.Standing)
    (Cw CS' Cη : ℝ) (hCw : 0 < Cw) (hCS' : 0 < CS') (hCη : 0 < Cη)
    (hw : ∀ᵐ s ∂M.ν0b, M.w s ≤ Cw)
    (hS' : M.obsLaw.map (fun o => o.2.2.2) ≤ ENNReal.ofReal CS' • M.ν0b)
    (hη : ∀ᵐ x ∂(M.ν0b ⊗ₘ M.πb), M.η x.1 x.2 ≤ Cη)
    (wh : S → ℝ) (hwh : Measurable wh) (hwhb : ∀ s, 0 ≤ wh s ∧ wh s ≤ Cw)
    (qh : S × A → ℝ) (hqh : Measurable qh)
    (hqhb : ∀ x, 0 ≤ qh x ∧ qh x ≤ M.Rmax / (1 - M.γ)) :
    |∫ o, M.ψ wh qh o ∂M.obsLaw - M.ρ| ≤
      (Cη + M.γ * Cη * √(CS' * Cη)) * M.normS (fun s => wh s - M.w s) *
        M.normSA (fun x => qh x - M.q x) := by sorry

end OffPolicyDRL.CrossFit
