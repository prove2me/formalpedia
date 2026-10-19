-- Prove2me | Theorems.Thm_OffPolicyDRL_CrossFit_term_28_op1
-- name    : OffPolicyDRL.CrossFit.term_28_op1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:11.980297+00:00
-- url     : https://prove2.me/theorems/ec1d5d98-ff7c-4163-a089-b8869e73fb10
-- title:
--   Proof of Thm 6, Term (28) is o_p(1): the centred fold empirical process at the opposite fold's nuisances vanishes
-- statement:
--   Let $O_0,O_1,\dots$ be i.i.d. observations with law $p_{\pi_b}$ on a probability space, and let the nuisance learners be measurable. Fix a fold $j\in\{0,1\}$, and let $\hat w^{[j]},\hat q^{[j]}$ be fitted on fold $j$. Assume the standing assumptions, $w\le C_w$ a.s., $p_{b,S'}\le C_{S'}p^{(0)}_{\pi_b}$ and $\eta\le C_\eta$ a.s. (bounded $\eta$ added). Assume (6b) for fold $j$: $0\le\hat q^{[j]}\le(1-\gamma)^{-1}R_{\max}$ and $0\le\hat w^{[j]}\le C_w$. Assume (6c) for fold $j$: $\|\hat w^{[j]}-w\|_2\to0$ and $\|\hat q^{[j]}-q\|_2\to0$ in probability. Let $n_{1-j}$ be the size of the other fold. Then, in probability as $n\to\infty$,
--   $$\frac{1}{\sqrt{n_{1-j}}}\sum_{i\in\text{fold }1-j}\Big(\psi(O_i;\hat w^{[j]},\hat q^{[j]})-\psi(O_i;w,q)-\big(\mathbb E_{O\sim p_{\pi_b}}[\psi(O;\hat w^{[j]},\hat q^{[j]})]-\mathbb E[\psi(O;w,q)]\big)\Big)\;\longrightarrow\;0 .$$
--   Here $\mathbb E_{O\sim p_{\pi_b}}[\psi(O;\hat w^{[j]},\hat q^{[j]})]$ is computed with the estimates frozen.
--
--   This is Term (28) of the decomposition (28)–(30). Because the nuisances come from the other fold, the centring is the conditional mean given that fold, and no complexity (Donsker) condition is needed.
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Appendix C, Proof of Theorems 6 and 7, Eq. (28) p. 59 and "Term (28) is op(1)", p. 60 (bounded η added)

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_Estimator

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

theorem term_28_op1 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace.CountablyGenerated A] (M : Model S A) (hM : M.Standing)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (O : ℕ → Ω → S × A × ℝ × S) (hO : ∀ i, Measurable (O i)) (hind : iIndepFun O μ)
    (hlaw : ∀ i, HasLaw (O i) M.obsLaw μ)
    (L : Learners S A) (hL : L.IsMeasurable)
    (Cw CS' Cη : ℝ) (hCw : 0 < Cw) (hCS' : 0 < CS') (hCη : 0 < Cη)
    (h6a_w : ∀ᵐ s ∂M.ν0b, M.w s ≤ Cw)
    (h6a_S' : M.obsLaw.map (fun o => o.2.2.2) ≤ ENNReal.ofReal CS' • M.ν0b)
    (hη : ∀ᵐ x ∂(M.ν0b ⊗ₘ M.πb), M.η x.1 x.2 ≤ Cη)
    (j : Fin 2)
    (h6b_q : ∀ n ω x, 0 ≤ qhat L O j n ω x ∧ qhat L O j n ω x ≤ M.Rmax / (1 - M.γ))
    (h6b_w : ∀ n ω s, 0 ≤ what L O j n ω s ∧ what L O j n ω s ≤ Cw)
    (h6c_w : TendstoInMeasure μ (fun n ω => errW M L O j n ω) atTop (fun _ => 0))
    (h6c_q : TendstoInMeasure μ (fun n ω => errQ M L O j n ω) atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => (√(foldSize (1 - j) n : ℝ))⁻¹ *
        ∑ k : Fin (foldSize (1 - j) n),
          (M.ψ (what L O j n ω) (qhat L O j n ω) (O (foldIdx (1 - j) n k) ω) -
            M.ψ M.w M.q (O (foldIdx (1 - j) n k) ω) -
            (∫ o, M.ψ (what L O j n ω) (qhat L O j n ω) o ∂M.obsLaw -
              ∫ o, M.ψ M.w M.q o ∂M.obsLaw)))
      atTop (fun _ => 0) := by sorry

end OffPolicyDRL.CrossFit
