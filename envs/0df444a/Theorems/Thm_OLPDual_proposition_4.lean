-- Prove2me | Theorems.Thm_OLPDual_proposition_4
-- name    : OLPDual.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:28.250964+00:00
-- url     : https://prove2.me/theorems/7e8c1915-e676-497b-a213-7769d971a9ec
-- title:
--   Proposition 4, p.13 (corrected: $\epsilon$ with $\underline d\epsilon^2\le\bar a\bar r\sqrt m$) — uniform quadratic lower bound (12)
-- statement:
--   Let $\mathcal P$ satisfy Assumptions 1 and 2 at the optimal solution $p^*$, let $n>m$, and let $\epsilon>0$ satisfy $\underline d\epsilon^2\le\bar a\bar r\sqrt m$. With probability at least
--
--   $$
--   1-m\exp\Bigl(-\frac{n\lambda_{\min}^2}{4\bar a^2}\Bigr)-2(2N)^m\exp\Bigl(-\frac{n\epsilon^2}{2}\Bigr),
--   $$
--
--   the following holds for all $p\in\Omega_p$:
--
--   $$
--   \frac1n\sum_{j=1}^n\int_{a_j^\top p}^{a_j^\top p^*}\bigl(I(r_j>v)-I(r_j>a_j^\top p^*)\bigr)\,dv\ge-\epsilon^2-2\epsilon\bar a\|p^*-p\|+\frac{\lambda\lambda_{\min}}{32}\|p^*-p\|^2.
--   $$
--
--   Here $N=\lfloor\log_q(\underline d\epsilon^2/(\bar a\bar r\sqrt m))\rfloor+1$ and $q=\max\{1/(1+\frac{1}{\sqrt m}),\,1/(1+\frac{1}{\sqrt m}(\frac{\lambda\lambda_{\min}}{8\mu\bar a^2})^{1/3})\}$.
--
--   This is the uniform control of the second-order term of (11). The domain condition on $\epsilon$ is equivalent to $N\ge 1$.
--
--   Differences from the source:
--   - correction: holds for any ϵ > 0 → ϵ > 0 with d̲ϵ² ≤ ā r̄ √m; reason: for larger ϵ, N ≤ 0 and for odd m the printed lower bound exceeds 1: m = 1, n = 2, a ≡ 10, r uniform on [0,1], d = 5, d̲ = 4, d̄ = 6, r̄ = 1, ā = 10, λ_min = 100, λ = 1/4, μ = 1, ϵ = √5 give N = −2 and ≈ 1.054
--   - encoding: ℙ(event of (12)) ≥ 1 − m·exp(…) − 2(2N)^m·exp(…) → the measure of the complement of the event is at most ofReal(m·exp(…) + 2(2N)^m·exp(…)); reason: the event quantifies over uncountably many p; the outer measure of its complement bounds its inner measure from below, the strong reading
--   - encoding: m the number of constraints → 1 ≤ m; reason: the paper indexes i = 1, …, m and divides by √m
--   - reading: λ_min is the minimum eigenvalue of M = E[aaᵀ]; Ξ satisfies Assumptions 1–2 → Model fixes positive r̄, ā, d̲ < d̄, λ, μ, λ_min, and λ_min is any lower bound on that eigenvalue; reason: p.13 says the parameters do not depend on 𝒫; the eigenvalue itself is one admissible value of lamMin
--   - encoding: (r, a) ∼ 𝒫 and ℙ(· | a) → the law of (a, r) is Pa ⊗ₘ κ with a Markov kernel κ, and Assumption 2 (b) reads ∀ p ∈ Ω_p, ∀ᵐ a; reason: every law on ℝ^m × ℝ disintegrates so; the order (a, r) fits Measure.compProd
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), Proposition 4, display (12), p.13; proof pp.34–40

import Mathlib
import Definitions.Def_OLPDual_Model
import Definitions.Def_OLPDual_EventE2

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OLPDual

/-- **Proposition 4, corrected**, Li–Ye, arXiv:1909.05499v5, p.13 (PDF 13), display (12): under
Assumptions 1–2, for `ε > 0` with `d̲ε² ≤ ā r̄ √m` and `n > m`, the bound (12) holds for all
`p ∈ Ω_p` with probability at least `1 − m exp(−nλ²_min/(4ā²)) − 2(2N)^m exp(−nε²/2)`.
**Formalization Note** The printed "any `ε > 0`" is false: for larger `ε`, `N ≤ 0` and the bound
exceeds 1. The statement bounds the outer measure of the complement of the event of (12), which
gives the lower bound on its inner measure (the event quantifies over uncountably many `p`). -/
theorem proposition_4 (Θ : Model) {m n : ℕ} (hm : 1 ≤ m) (hn : m < n) (d : E m)
    (Pa : Measure (E m)) [IsProbabilityMeasure Pa] (κ : Kernel (E m) ℝ) [IsMarkovKernel κ]
    (pstar : E m) (hA1 : Assumption1 Θ d (Pa ⊗ₘ κ))
    (hmin : IsOptimal (f d (Pa ⊗ₘ κ)) pstar) (hA2 : Assumption2 Θ d Pa κ pstar)
    {ε : ℝ} (hε : 0 < ε) (hεN : Θ.dlow * ε ^ 2 ≤ Θ.abar * Θ.rbar * Real.sqrt m) :
    sampleLaw (Pa ⊗ₘ κ) n (EventE2 Θ pstar ε n)ᶜ ≤
      ENNReal.ofReal
        ((m : ℝ) * Real.exp (-((n : ℝ) * Θ.lamMin ^ 2) / (4 * Θ.abar ^ 2)) +
          2 * (2 * (covLayers Θ m ε : ℝ)) ^ m * Real.exp (-((n : ℝ) * ε ^ 2) / 2)) := by sorry

end OLPDual
