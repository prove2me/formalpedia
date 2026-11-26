-- Prove2me | Theorems.Thm_OnlineUBSR_Supplement_theorem_3
-- name    : OnlineUBSR.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:41:11.119451+00:00
-- url     : https://prove2.me/theorems/899c7fa5-9109-41db-a2fb-5d9587627318
-- title:
--   Theorem 3 (corrected: base assumptions and literal big-O) — universal step-size bounds
-- statement:
--   Under Assumptions 1–4, Theorem 3 gives both printed cases. For $a_k=c/k$, the mean-squared error is bounded by the displayed initial-error term plus a function $\mathcal K_1(n)$ having the stated three big-$O$ regimes according as $\mu_1c<1$, $=1$, or $>1$. For $a_k=c/k^\alpha$, $0<\alpha<1$, it satisfies the explicit exponentially decaying plus $n^{-\alpha}$ bound printed on p.6. Each case uses its own condition $a_{n_0}L_1^2<\mu_1$ and holds for every $n\ge n_0$.
--
--   This theorem supplies a step-size choice that does not require tuning $c$ from the unknown monotonicity constant.
--
--   Differences from the source:
--   - correction: Assumption 3 bounds $-\ell'(-t)$ → Lean bounds $g'(t)$; reason: the proof uses $g'$ and the printed condition is false for nonzero $X$
--   - correction: Assumption 4 starts at $n\ge1$ → Lean includes $n=0$; reason: the first recursion step uses it
--   - correction: the source leaves $t_0$ unrestricted → Lean requires $t_0\in[t_l,t_u]$; reason: the proof uses interval control at the initial point
--   - encoding: $\mathcal K_1(n)=O(r(n))$ is informal asymptotic notation → Lean existentially quantifies $\mathcal K_1$ and uses filter big-$O$ at infinity in each printed regime; reason: this is the literal mathematical content of the notation
--   - encoding: one theorem presents two choices of $a_k$ after choosing $n_0$ → Lean states two implications, each with its own Assumption 4 and $a_{n_0}L_1^2<\mu_1$ premise; reason: the two step sequences give different premises and neither case should require the other's
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Theorem 3, p.6

import Mathlib
import Definitions.Def_OnlineUBSR_Supplement_Model

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology

namespace OnlineUBSR.Supplement

/-- **Theorem 3 (universal polynomial step sizes).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Theorem 3, p.6.

**Formalization Note.** Each case has its own instance of Assumption 4 and its own literal
condition `a n₀ L₁²<μ₁`; writing the theorem as two implications avoids requiring a single
`n₀` to satisfy both unrelated step choices. The unspecified `𝒦₁(n)=O(·)` in Case I is an
existential function with the printed three asymptotic regimes. The three base corrections are
the same as in Theorem 1. -/
theorem theorem_3
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X)
    (ξ : ℕ → Ω → ℝ) (hξ : ∀ n, Measurable (ξ (n + 1)))
    (hind : iIndepFun (fun n => ξ (n + 1)) μ)
    (hident : ∀ n, IdentDistrib (ξ (n + 1)) (fun ω => -X ω) μ μ)
    (ℓ : ℝ → ℝ) (hℓconv : ConvexOn ℝ Set.univ ℓ) (hℓdiff : Differentiable ℝ ℓ)
    (lam tl tu : ℝ) (htlu : tl < tu)
    (hA1l : 0 < OnlineUBSR.gFun μ ℓ lam X tl)
    (hA1u : OnlineUBSR.gFun μ ℓ lam X tu < 0)
    (M₀ : ℝ) (hA2 : ∀ᵐ ω ∂μ, |X ω| ≤ M₀)
    (μ₁ L₁ : ℝ) (hμ₁ : 0 < μ₁) (hL₁ : 0 < L₁)
    (hA3 : ∀ t ∈ Set.Icc tl tu,
      -L₁ ≤ deriv (OnlineUBSR.gFun μ ℓ lam X) t ∧
        deriv (OnlineUBSR.gFun μ ℓ lam X) t ≤ -μ₁)
    (σ : ℝ) (hσ : 0 < σ) (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Icc tl tu)
    (c : ℝ) (hc : 0 < c) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) :
    ((c / (n₀ : ℝ) * L₁ ^ 2 < μ₁ ∧
        EstimationNoiseBound μ ℓ lam tl tu t₀ σ X (fun k : ℕ => c / (k : ℝ)) ξ) →
      ∃ K₁ : ℕ → ℝ,
        K₁ =O[atTop] (fun n : ℕ =>
          if μ₁ * c < 1 then 1 / (n : ℝ) ^ (μ₁ * c)
          else if μ₁ * c = 1 then Real.log n / n
          else 1 / (n : ℝ)) ∧
        ∀ n : ℕ, n₀ ≤ n →
          ∫ ω, (OnlineUBSR.iterate ℓ lam tl tu t₀ (fun k : ℕ => c / (k : ℝ)) ξ n ω -
              OnlineUBSR.ubsr μ ℓ lam X) ^ 2 ∂μ ≤
            (1 + c * L₁) ^ (2 * n₀) * (n₀ + 1 : ℝ) ^ (μ₁ * c) *
                ((t₀ - OnlineUBSR.ubsr μ ℓ lam X) ^ 2 + σ ^ 2 * Real.pi ^ 2 / 6) /
                (n : ℝ) ^ (μ₁ * c) + K₁ n) ∧
    ((c / (n₀ : ℝ) ^ α * L₁ ^ 2 < μ₁ ∧
        EstimationNoiseBound μ ℓ lam tl tu t₀ σ X
          (fun k : ℕ => c / (k : ℝ) ^ α) ξ) →
      ∀ n : ℕ, n₀ ≤ n →
        ∫ ω, (OnlineUBSR.iterate ℓ lam tl tu t₀ (fun k : ℕ => c / (k : ℝ) ^ α) ξ n ω -
            OnlineUBSR.ubsr μ ℓ lam X) ^ 2 ∂μ ≤
          ((1 + c * L₁) ^ (2 * n₀) *
              Real.exp (μ₁ * c * (n₀ : ℝ) ^ (1 - α) / (1 - α))) *
            ((t₀ - OnlineUBSR.ubsr μ ℓ lam X) ^ 2 + σ ^ 2 * c ^ 2 * n₀) *
              Real.exp (-(μ₁ * c * (n : ℝ) ^ (1 - α) / (1 - α))) +
            2 * σ ^ 2 * c ^ 2 * (μ₁ * c) ^ (α / (1 - α)) /
              ((1 - α) * (n : ℝ) ^ α)) := by sorry

end OnlineUBSR.Supplement
