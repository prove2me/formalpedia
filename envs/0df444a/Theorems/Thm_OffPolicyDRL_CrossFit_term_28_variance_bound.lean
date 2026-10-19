-- Prove2me | Theorems.Thm_OffPolicyDRL_CrossFit_term_28_variance_bound
-- name    : OffPolicyDRL.CrossFit.term_28_variance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:44.77144+00:00
-- url     : https://prove2.me/theorems/e5875a78-5a2b-4378-905f-30d68dfc971a
-- title:
--   Proof of Thm 6, Term (28): var[ψ(ŵ, q̂) − ψ(w, q)] ≤ 2a²‖ŵ − w‖₂² + 2b²‖q̂ − q‖₂² (explicit constants; η bounded)
-- statement:
--   Under the hypotheses of the Term (30) bound ($w\le C_w$, $p_{b,S'}\le C_{S'}p^{(0)}_{\pi_b}$, $\eta\le C_\eta$; measurable $\hat w,\hat q$ with $0\le\hat w\le C_w$, $0\le\hat q\le(1-\gamma)^{-1}R_{\max}$), and with $(s,a,r,s')\sim p_{\pi_b}$,
--   $$\operatorname{var}\big[\psi(s,a,r,s';\hat w,\hat q)-\psi(s,a,r,s';w,q)\big]\le 2a^2\|\hat w-w\|_2^2+2b^2\|\hat q-q\|_2^2,$$
--   where
--   $$a=\frac{C_\eta R_{\max}}{1-\gamma},\qquad b=C_wC_\eta\big(1+\gamma\sqrt{C_{S'}C_\eta}\big).$$
--
--   This is the variance bound behind Term (28). The fluctuation of the empirical process at the estimated nuisances, minus the oracle one, vanishes when both nuisance errors do.
--
--   **Formalization Note** The paper writes only $\operatorname{var}[\cdot\mid\mathcal D_1]\le\mathbb E[D_1^2+D_2^2+D_3^2+2D_1D_2+2D_2D_3+2D_1D_3\mid\mathcal D_1]=o_p(1)$. The explicit constants $a$ and $b$ are this formalization's. The constant term $(1-\gamma)\mathbb E_{p^{(0)}_{\pi_e}}[\hat v-v]$ cancels in the variance.
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Appendix C, Proof of Theorems 6 and 7, "Term (28) is op(1)", display of the conditional variance, p. 60 (explicit constants; η bounded added)

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

theorem term_28_variance_bound {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace.CountablyGenerated A] (M : Model S A) (hM : M.Standing)
    (Cw CS' Cη : ℝ) (hCw : 0 < Cw) (hCS' : 0 < CS') (hCη : 0 < Cη)
    (hw : ∀ᵐ s ∂M.ν0b, M.w s ≤ Cw)
    (hS' : M.obsLaw.map (fun o => o.2.2.2) ≤ ENNReal.ofReal CS' • M.ν0b)
    (hη : ∀ᵐ x ∂(M.ν0b ⊗ₘ M.πb), M.η x.1 x.2 ≤ Cη)
    (wh : S → ℝ) (hwh : Measurable wh) (hwhb : ∀ s, 0 ≤ wh s ∧ wh s ≤ Cw)
    (qh : S × A → ℝ) (hqh : Measurable qh)
    (hqhb : ∀ x, 0 ≤ qh x ∧ qh x ≤ M.Rmax / (1 - M.γ)) :
    variance (fun o => M.ψ wh qh o - M.ψ M.w M.q o) M.obsLaw ≤
      2 * (Cη * M.Rmax / (1 - M.γ)) ^ 2 * M.normS (fun s => wh s - M.w s) ^ 2 +
        2 * (Cw * Cη * (1 + M.γ * √(CS' * Cη))) ^ 2 *
          M.normSA (fun x => qh x - M.q x) ^ 2 := by sorry

end OffPolicyDRL.CrossFit
