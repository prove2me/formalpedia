-- Prove2me | Theorems.Thm_OLPDual_theorem_1
-- name    : OLPDual.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:13.12098+00:00
-- url     : https://prove2.me/theorems/74c9b222-8f91-4eff-9e22-55930ee36d88
-- title:
--   Theorem 1, p.13 — dual convergence: $\mathbb E\|p_n^*-p^*\|^2\le Cm\log m\log\log n/n$
-- statement:
--   Fix the parameters $\bar r,\bar a,\underline d<\bar d,\lambda,\mu,\lambda_{\min}$ of the family $\Xi$ of laws satisfying Assumptions 1 and 2. There is a constant $C$, depending only on these parameters, such that for all $m\ge 2$, all $n\ge\max\{m,3\}$, every $d$ in the capacity box and every $\mathcal P\in\Xi$, with $p^*$ the optimal solution of (7) and $p_n^*$ any optimal solution of (6) on an i.i.d. sample of size $n$ from $\mathcal P$,
--
--   $$
--   \mathbb E\bigl[\|p_n^*-p^*\|^2\bigr]\le\frac{Cm\log m\log\log n}{n},\qquad
--   \mathbb E\bigl[\|p_n^*-p^*\|\bigr]\le C\sqrt{\frac{m\log m\log\log n}{n}}.
--   $$
--
--   For $m=1$, both bounds hold without the $\log m$ term.
--
--   This is the main result of the first half of the paper: the optimal solution of the sampled dual LP converges to the optimal solution of the stochastic program at an explicit finite-sample rate, for general linear programs.
--
--   **Formalization Note** `gFactor m` is $m\log m$ for $m\ge 2$ and $1$ for $m=1$. The constant is quantified after `Θ` and before $m$, $n$, $d$ and the law.
--
--   Differences from the source:
--   - reading: λ_min is the minimum eigenvalue of M = E[aaᵀ]; Ξ satisfies Assumptions 1–2 → Model fixes positive r̄, ā, d̲ < d̄, λ, μ, λ_min, and λ_min is any lower bound on that eigenvalue; reason: p.13 says the parameters do not depend on 𝒫; the eigenvalue itself is one admissible value of lamMin
--   - generalization: Assumption 1 (d), n > m → dropped; n ≥ max{m, 3}; reason: Theorem 1 itself prints n ≥ max{m, 3}, which contains every n > m ≥ 2 with n ≥ 3
--   - generalization: p*_n the optimal solution of (6) → phat any measurable map that is a minimizer of f_n for almost every sample; reason: every measurable selection of optimal solutions is such a map
--   - encoding: (r, a) ∼ 𝒫 and ℙ(· | a) → the law of (a, r) is Pa ⊗ₘ κ with a Markov kernel κ, and Assumption 2 (b) reads ∀ p ∈ Ω_p, ∀ᵐ a; reason: every law on ℝ^m × ℝ disintegrates so; the order (a, r) fits Measure.compProd
--   - encoding: E[·] → lower Lebesgue integrals of ENNReal.ofReal; reason: the integrands are nonnegative; no Bochner junk value
--   - encoding: the sentence on m = 1 (p.14) → gFactor 1 = 1 inside one statement; reason: same two bounds, one C ("we adopt the same constant for both inequalities", p.14)
--   - encoding: there exists a constant C → ∃ C with 0 < C; reason: the bounds are monotone in C, so the two forms are equivalent
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), Theorem 1, p.13, and the m = 1 clause, p.14; proof pp.40–42

import Mathlib
import Definitions.Def_OLPDual_Model

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OLPDual

/-- **Theorem 1**, Li–Ye, arXiv:1909.05499v5, p.13 (PDF 13), with the `m = 1` clause of p.14:
under Assumptions 1 and 2 there is a constant `C` with
`E‖p*_n − p*‖² ≤ C m log m log log n / n` and `E‖p*_n − p*‖ ≤ C √(m log m log log n / n)` for all
`n ≥ max{m, 3}`, `m ≥ 2` and `𝒫 ∈ Ξ`; for `m = 1` both hold without the `log m` term.
**Formalization Note** `C` depends only on the parameters `Θ` of the family `Ξ`, not on `m`, `n`,
`d` or the law. `phat` is any measurable selection of optimal solutions of (6), required almost
surely. The law of `(a, r)` is `Pa ⊗ₘ κ`. Expectations are lower Lebesgue integrals of
`ENNReal.ofReal`, so they carry no junk value. -/
theorem theorem_1 (Θ : Model) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ), 1 ≤ m → max m 3 ≤ n →
      ∀ (d : E m) (Pa : Measure (E m)) [IsProbabilityMeasure Pa] (κ : Kernel (E m) ℝ)
        [IsMarkovKernel κ] (pstar : E m),
        Assumption1 Θ d (Pa ⊗ₘ κ) → IsOptimal (f d (Pa ⊗ₘ κ)) pstar →
        Assumption2 Θ d Pa κ pstar →
        ∀ phat : Sample m n → E m, Measurable phat →
          (∀ᵐ ω ∂(sampleLaw (Pa ⊗ₘ κ) n), IsOptimal (fn d ω) (phat ω)) →
          ∫⁻ ω, ENNReal.ofReal (‖phat ω - pstar‖ ^ 2) ∂(sampleLaw (Pa ⊗ₘ κ) n) ≤
              ENNReal.ofReal (C * gFactor m * Real.log (Real.log n) / n) ∧
            ∫⁻ ω, ENNReal.ofReal ‖phat ω - pstar‖ ∂(sampleLaw (Pa ⊗ₘ κ) n) ≤
              ENNReal.ofReal (C * Real.sqrt (gFactor m * Real.log (Real.log n) / n)) := by sorry

end OLPDual
