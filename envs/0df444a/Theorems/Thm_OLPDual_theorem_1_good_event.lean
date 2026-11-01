-- Prove2me | Theorems.Thm_OLPDual_theorem_1_good_event
-- name    : OLPDual.theorem_1_good_event
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:19.485981+00:00
-- url     : https://prove2.me/theorems/7ad263e1-4a42-4fde-96cb-711d73547753
-- title:
--   Proof of Theorem 1, display (30), pp.40–41 — on $\mathcal E_1\cap\mathcal E_2$, (30) holds and $\|p_n^*-p^*\|\le\kappa\epsilon$
-- statement:
--   Let $\mathcal P$ satisfy Assumptions 1 and 2 at $p^*$, let $\epsilon>0$, and fix a sample in $\mathcal E_1\cap\mathcal E_2$. Then for all $p\in\Omega_p$,
--
--   $$
--   f_n(p)-f_n(p^*)\ge-\epsilon^2-\epsilon(2\bar a+1)\|p^*-p\|+\frac{\lambda\lambda_{\min}}{32}\|p^*-p\|^2,
--   $$
--
--   and every minimizer $p_n^*$ of $f_n$ over $p\ge 0$ that lies in $\Omega_p$ satisfies $\|p_n^*-p^*\|\le\kappa\epsilon$, with
--
--   $$
--   \kappa=\frac{2\bar a+1+\sqrt{(2\bar a+1)^2+\lambda\lambda_{\min}/8}}{\lambda\lambda_{\min}/16}.
--   $$
--
--   This turns the two high-probability events into the deterministic bound that is integrated in the proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: p*_n lies in Ω_p by Proposition 1 (c), with probability 1 → phat ∈ OmegaP is a hypothesis; reason: the statement concerns one fixed sample; Proposition 1 (c) supplies it almost surely
--   - generalization: Assumption 1 (d), n > m → n ≥ 1; reason: n > m ≥ 1 implies n ≥ 1 and the result does not use n > m
--   - reading: λ_min is the minimum eigenvalue of M = E[aaᵀ]; Ξ satisfies Assumptions 1–2 → Model fixes positive r̄, ā, d̲ < d̄, λ, μ, λ_min, and λ_min is any lower bound on that eigenvalue; reason: p.13 says the parameters do not depend on 𝒫; the eigenvalue itself is one admissible value of lamMin
--   - encoding: (r, a) ∼ 𝒫 and ℙ(· | a) → the law of (a, r) is Pa ⊗ₘ κ with a Markov kernel κ, and Assumption 2 (b) reads ∀ p ∈ Ω_p, ∀ᵐ a; reason: every law on ℝ^m × ℝ disintegrates so; the order (a, r) fits Measure.compProd
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), proof of Theorem 1, display (30), p.40, and the bound ‖p*_n − p*‖ ≤ κϵ, p.41

import Mathlib
import Definitions.Def_OLPDual_Model
import Definitions.Def_OLPDual_EventE2

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OLPDual

/-- **Proof of Theorem 1, display (30) and the bound `‖p*_n − p*‖ ≤ κε`**, Li–Ye,
arXiv:1909.05499v5, pp.40–41 (PDF 40–41). On `ℰ₁ ∩ ℰ₂`, for all `p ∈ Ω_p`,
`f_n(p) − f_n(p*) ≥ −ε² − ε(2ā + 1)‖p* − p‖ + (λλ_min/32)‖p* − p‖²`, and every minimizer of `f_n`
over `p ≥ 0` that lies in `Ω_p` is within `κε` of `p*`.
**Formalization Note** A deterministic statement about one sample. Minimizers lie in `Ω_p` with
probability 1 by Proposition 1 (c); membership is a hypothesis here because the statement is about
a single sample. -/
theorem theorem_1_good_event (Θ : Model) {m n : ℕ} (hn : 0 < n) (d : E m) (Pa : Measure (E m))
    [IsProbabilityMeasure Pa] (κ : Kernel (E m) ℝ) [IsMarkovKernel κ] (pstar : E m)
    (hA1 : Assumption1 Θ d (Pa ⊗ₘ κ)) (hmin : IsOptimal (f d (Pa ⊗ₘ κ)) pstar)
    (hA2 : Assumption2 Θ d Pa κ pstar) {ε : ℝ} (hε : 0 < ε) (ω : Sample m n)
    (hE1 : ω ∈ EventE1 d (Pa ⊗ₘ κ) pstar ε n) (hE2 : ω ∈ EventE2 Θ pstar ε n) :
    (∀ p ∈ OmegaP Θ m,
      -ε ^ 2 - ε * (2 * Θ.abar + 1) * ‖pstar - p‖ + Θ.lam * Θ.lamMin / 32 * ‖pstar - p‖ ^ 2 ≤
        fn d ω p - fn d ω pstar) ∧
    ∀ phat ∈ OmegaP Θ m, IsOptimal (fn d ω) phat → ‖phat - pstar‖ ≤ kappa Θ * ε := by sorry

end OLPDual
