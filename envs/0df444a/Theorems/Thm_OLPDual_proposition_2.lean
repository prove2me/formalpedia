-- Prove2me | Theorems.Thm_OLPDual_proposition_2
-- name    : OLPDual.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:18.435555+00:00
-- url     : https://prove2.me/theorems/e591a932-2993-4ce1-9380-0563d743522e
-- title:
--   Proposition 2, p.11 — growth and smoothness (10) on $\Omega_p$, and uniqueness of $p^*$
-- statement:
--   Let $\mathcal P$ satisfy Assumptions 1 and 2 at an optimal solution $p^*$ of the stochastic program (7). For every $p\in\Omega_p$,
--
--   $$
--   \frac{\lambda\lambda_{\min}}{2}\|p-p^*\|^2\le f(p)-f(p^*)-\nabla f(p^*)^\top(p-p^*)\le\frac{\mu\bar a^2}{2}\|p-p^*\|^2.
--   $$
--
--   Moreover, the optimal solution $p^*$ of (7) is unique.
--
--   The role of Assumption 2 is thus to impose local strong convexity and local smoothness of $f$ around $p^*$. The uniqueness makes convergence to $p^*$ well defined.
--
--   Differences from the source:
--   - reading: λ_min is the minimum eigenvalue of M = E[aaᵀ]; Ξ satisfies Assumptions 1–2 → Model fixes positive r̄, ā, d̲ < d̄, λ, μ, λ_min, and λ_min is any lower bound on that eigenvalue; reason: p.13 says the parameters do not depend on 𝒫; the eigenvalue itself is one admissible value of lamMin
--   - encoding: (r, a) ∼ 𝒫 and ℙ(· | a) → the law of (a, r) is Pa ⊗ₘ κ with a Markov kernel κ, and Assumption 2 (b) reads ∀ p ∈ Ω_p, ∀ᵐ a; reason: every law on ℝ^m × ℝ disintegrates so; the order (a, r) fits Measure.compProd
--   - encoding: p* is unique → every minimizer q of f over p ≥ 0 equals pstar; reason: the same statement, given that pstar is a minimizer
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), Proposition 2, display (10), p.11; proof pp.32–33

import Mathlib
import Definitions.Def_OLPDual_Model

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OLPDual

/-- **Proposition 2 (Growth and Smoothness of `f(p)`)**, Li–Ye, arXiv:1909.05499v5, p.11 (PDF 11),
display (10). Under Assumptions 1 and 2, for `p ∈ Ω_p`,
`λλ_min/2 ‖p − p*‖² ≤ f(p) − f(p*) − ∇f(p*)ᵀ(p − p*) ≤ μā²/2 ‖p − p*‖²`; moreover the optimal
solution `p*` of (7) is unique. -/
theorem proposition_2 (Θ : Model) {m : ℕ} (d : E m) (Pa : Measure (E m)) [IsProbabilityMeasure Pa]
    (κ : Kernel (E m) ℝ) [IsMarkovKernel κ] (pstar : E m) (hA1 : Assumption1 Θ d (Pa ⊗ₘ κ))
    (hmin : IsOptimal (f d (Pa ⊗ₘ κ)) pstar) (hA2 : Assumption2 Θ d Pa κ pstar) :
    (∀ p ∈ OmegaP Θ m,
      Θ.lam * Θ.lamMin / 2 * ‖p - pstar‖ ^ 2 ≤
          f d (Pa ⊗ₘ κ) p - f d (Pa ⊗ₘ κ) pstar - ⟪gradf d (Pa ⊗ₘ κ) pstar, p - pstar⟫ ∧
        f d (Pa ⊗ₘ κ) p - f d (Pa ⊗ₘ κ) pstar - ⟪gradf d (Pa ⊗ₘ κ) pstar, p - pstar⟫ ≤
          Θ.mu * Θ.abar ^ 2 / 2 * ‖p - pstar‖ ^ 2) ∧
    ∀ q, IsOptimal (f d (Pa ⊗ₘ κ)) q → q = pstar := by sorry

end OLPDual
