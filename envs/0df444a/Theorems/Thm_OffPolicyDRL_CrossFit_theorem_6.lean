-- Prove2me | Theorems.Thm_OffPolicyDRL_CrossFit_theorem_6
-- name    : OffPolicyDRL.CrossFit.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:04.152124+00:00
-- url     : https://prove2.me/theorems/1dd1fbe3-3615-47d4-b4c6-98ef0a85c6e9
-- title:
--   Theorem 6 — cross-fitted ρ̂_DRL(M3) is asymptotically linear with influence function φ_eff and √n(ρ̂_DRL(M3) − ρ^{πe}) →d N(0, EB(M3)) (η bounded added)
-- statement:
--   **Theorem 6 (Efficiency of $\hat\rho_{\rm DRL}(\mathcal M_3)$ under transition sampling: cross-fitting).**
--
--   Consider the off-policy evaluation model under its standing assumptions:
--   - Markov transition and reward kernels on measurable state and action spaces, the action σ-algebra countably generated;
--   - rewards in $[0,R_{\max}]$ and $0\le\gamma<1$;
--   - Markov target and behavior policies $\pi_e,\pi_b$, and probability laws $p^{(0)}_{\pi_e}$, $p^{(0)}_{\pi_b}$;
--   - overlap: $\pi_e(\cdot\mid s)\ll\pi_b(\cdot\mid s)$ and $p^{(\infty)}_{\pi_e,\gamma}\ll p^{(0)}_{\pi_b}$.
--
--   Let $O_i=(s^{\langle i\rangle},a^{\langle i\rangle},r^{\langle i\rangle},s'^{\langle i\rangle})$, $i\ge0$, be independent observations, each with law $p_{\pi_b}$. Let $\hat w^{[j]},\hat q^{[j]}$ ($j=0,1$) be produced by jointly measurable learners from the data of fold $j$ only. Let $\hat\rho_{\rm DRL}(\mathcal M_3)$ be the cross-fitted estimator of Eq. (4). Assume:
--
--   - **(6a)** there are constants $C_w,C_{S'}>0$ with $w\le C_w$ ($p^{(0)}_{\pi_b}$-a.s.) and $p_{b,S'}\le C_{S'}\,p_{b,S}$, where $p_{b,S}=p^{(0)}_{\pi_b}$ and $p_{b,S'}$ are the laws of $s$ and $s'$ in the data;
--   - **(added)** there is $C_\eta>0$ with $\eta\le C_\eta$ ($p^{(0)}_{\pi_b}\otimes\pi_b$-a.s.);
--   - **(6b)** $0\le\hat q^{[j]}\le(1-\gamma)^{-1}R_{\max}$ and $0\le\hat w^{[j]}\le C_w$ for $j=0,1$;
--   - **(6c)** $\|\hat w^{[j]}-w\|_2=o_p(1)$ and $\|\hat q^{[j]}-q\|_2=o_p(1)$ for $j=0,1$;
--   - **(6d)** $\sqrt n\,\|\hat w^{[j]}-w\|_2\,\|\hat q^{[j]}-q\|_2=o_p(1)$ for $j=0,1$.
--
--   Then:
--
--   1. the estimator is asymptotically linear with influence function $\phi_{\rm eff}$:
--   $$\sqrt n\big(\hat\rho_{\rm DRL}(\mathcal M_3)-\rho^{\pi_e}\big)-\frac1{\sqrt n}\sum_{i=0}^{n-1}\phi_{\rm eff}(O_i)\;\xrightarrow{\;p\;}\;0;$$
--   2. it is asymptotically normal at the efficiency bound:
--   $$\sqrt n\big(\hat\rho_{\rm DRL}(\mathcal M_3)-\rho^{\pi_e}\big)\xrightarrow{\;d\;}N\big(0,\mathrm{EB}(\mathcal M_3)\big),\qquad \mathrm{EB}(\mathcal M_3)=\mathbb E\big[w^2(s)\eta^2(s,a)(r+\gamma v(s')-q(s,a))^2\big].$$
--
--   The theorem says that, with cross-fitting, any black-box nuisance estimators with the product rate $o_p(n^{-1/2})$ yield an estimator that attains the MDP efficiency bound. Its variance shrinks with the number of transitions, not the number of trajectories.
--
--   **Formalization Note** The paper's rate bounds $\kappa^w_n,\kappa^q_n$ are existential. The rates are stated directly on the random $L^2$ errors (take $\kappa$ to be the error), as convergence in probability. (6d) is required only for same-fold products, which is all the proof uses. A bound on $\eta$ is added: without it the Jensen step and the Term (30) bound of the proof fail, and $\mathrm{EB}(\mathcal M_3)$ can be infinite. "RAL and efficient" is rendered as asymptotic linearity with the efficient influence function plus the normal limit. Regularity requires the semiparametric framework of Theorem 3 and is not stated. The normal limit is stated as convergence in distribution to any random variable $Z$ with law $N(0,\mathrm{EB}(\mathcal M_3))$.
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Theorem 6, p. 23; proof in Appendix C, Proof of Theorems 6 and 7, pp. 59–60 (corrected: bounded η added)

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_Estimator

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

theorem theorem_6 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace.CountablyGenerated A] (M : Model S A) (hM : M.Standing)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (O : ℕ → Ω → S × A × ℝ × S) (hO : ∀ i, Measurable (O i)) (hind : iIndepFun O μ)
    (hlaw : ∀ i, HasLaw (O i) M.obsLaw μ)
    (L : Learners S A) (hL : L.IsMeasurable)
    (Cw CS' Cη : ℝ) (hCw : 0 < Cw) (hCS' : 0 < CS') (hCη : 0 < Cη)
    (h6a_w : ∀ᵐ s ∂M.ν0b, M.w s ≤ Cw)
    (h6a_S' : M.obsLaw.map (fun o => o.2.2.2) ≤ ENNReal.ofReal CS' • M.ν0b)
    (hη : ∀ᵐ x ∂(M.ν0b ⊗ₘ M.πb), M.η x.1 x.2 ≤ Cη)
    (h6b_q : ∀ j n ω x, 0 ≤ qhat L O j n ω x ∧ qhat L O j n ω x ≤ M.Rmax / (1 - M.γ))
    (h6b_w : ∀ j n ω s, 0 ≤ what L O j n ω s ∧ what L O j n ω s ≤ Cw)
    (h6c_w : ∀ j, TendstoInMeasure μ (fun n ω => errW M L O j n ω) atTop (fun _ => 0))
    (h6c_q : ∀ j, TendstoInMeasure μ (fun n ω => errQ M L O j n ω) atTop (fun _ => 0))
    (h6d : ∀ j k : Fin 2, TendstoInMeasure μ
      (fun (n : ℕ) ω => √(n : ℝ) * errW M L O j n ω * errQ M L O k n ω) atTop (fun _ => 0))
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (Z : Ω' → ℝ) (hZ : HasLaw Z (gaussianReal 0 M.EB.toNNReal) μ') :
    TendstoInMeasure μ
        (fun (n : ℕ) ω => √(n : ℝ) * (estimate M L O n ω - M.ρ) -
          (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, M.φeff (O i ω))
        atTop (fun _ => 0) ∧
      TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (estimate M L O n ω - M.ρ)) atTop Z
        (fun _ => μ) μ' := by sorry

end OffPolicyDRL.CrossFit
