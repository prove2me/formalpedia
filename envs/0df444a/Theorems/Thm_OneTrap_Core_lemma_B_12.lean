-- Prove2me | Theorems.Thm_OneTrap_Core_lemma_B_12
-- name    : OneTrap.Core.lemma_B_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:44:19.679209+00:00
-- url     : https://prove2.me/theorems/0a45989e-a4e2-4d15-b267-e83eb831ff88
-- title:
--   Lemma B.12 — $\mathbb E[(X-r)^+]$: continuity, monotonicity, 1-Lipschitz, layer-cake increments, unique root at level $c>0$, smallest extended root $\operatorname{ess\,sup}X$ at $0$
-- statement:
--   Let $X$ be an integrable nonnegative random variable on a probability space and $\varphi(r)=\mathbb E[(X-r)^+]$. Then $\varphi$ is continuous, nonincreasing and $1$-Lipschitz; for $r_1<r_2$,
--   $$\varphi(r_1)-\varphi(r_2)=\int_{r_1}^{r_2}\mathbb P(X>s)\,ds;$$
--   for $c>0$ the equation $\varphi(r)=c$ has a unique finite solution; and the smallest extended-real solution of $\varphi(r)=0$ (with $(X-\infty)^+:=0$) is $\operatorname{ess\,sup}X$, possibly $+\infty$.
--
--   Differences from the source:
--   - encoding: an integrable nonnegative wage X → `X : Ω → ℝ` on a probability space `(Ω, μ)` with `Integrable X μ` and `0 ≤ X` almost surely; reason: a generic random variable
--   - encoding: ϕ(r) = E[(X − r)+] and P(X > s) → the Bochner integral `∫ max (X − r) 0 ∂μ` and `(μ {s < X}).toReal`, with the identity as an interval integral; reason: (X − r)+ ≤ X + |r| is integrable, so the Bochner integral is the expectation (no junk value)
--   - encoding: its smallest extended-real solution (of ϕ(r) = 0) is ess sup X → `IsLeast {r : EReal | ∫⁻ ((X : EReal) − r).toENNReal ∂μ = 0} (essSup (X : EReal) μ)`; reason: ϕ extended to EReal with (X − ∞)+ = 0 (EReal subtraction gives X − ⊤ = ⊥) and (X + ∞)+ = ∞
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Lemma B.12, p. 32 (PDF 33)

import Mathlib

open MeasureTheory

namespace OneTrap.Core

/-- Lemma B.12 (p. 32). For an integrable nonnegative wage `X`, `ϕ(r) = E[(X − r)⁺]` is
continuous, nonincreasing and 1-Lipschitz; for `r₁ < r₂`,
`ϕ(r₁) − ϕ(r₂) = ∫_{r₁}^{r₂} P(X > s) ds`; for `c > 0`, `ϕ(r) = c` has a unique finite
solution; and the smallest extended-real solution of `E[(X − r)⁺] = 0` (with `(X − ∞)⁺ = 0`) is
`ess sup X`. -/
theorem lemma_B_12 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXint : Integrable X μ) (hXnonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω) :
    (Continuous (fun r : ℝ => ∫ ω, max (X ω - r) 0 ∂μ) ∧
      Antitone (fun r : ℝ => ∫ ω, max (X ω - r) 0 ∂μ) ∧
      LipschitzWith 1 (fun r : ℝ => ∫ ω, max (X ω - r) 0 ∂μ)) ∧
    (∀ r₁ r₂ : ℝ, r₁ < r₂ →
      (∫ ω, max (X ω - r₁) 0 ∂μ) - (∫ ω, max (X ω - r₂) 0 ∂μ) =
        ∫ s in r₁..r₂, (μ {ω | s < X ω}).toReal) ∧
    (∀ c : ℝ, 0 < c → ∃! r : ℝ, (∫ ω, max (X ω - r) 0 ∂μ) = c) ∧
    IsLeast {r : EReal | ∫⁻ ω, (((X ω : ℝ) : EReal) - r).toENNReal ∂μ = 0}
      (essSup (fun ω => ((X ω : ℝ) : EReal)) μ) := by sorry

end OneTrap.Core
