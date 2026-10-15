-- Prove2me | Theorems.Thm_LNChannels_Exact_first_term
-- name    : LNChannels.Exact.first_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:23.367477+00:00
-- url     : https://prove2.me/theorems/bcf7cc99-1783-4ace-9375-621d9b1a4244
-- title:
--   Proof of Theorem 1, p. 10 — $E[e^{-r\tau}]$ and the expected opportunity cost until the next payment
-- statement:
--   Let $\tau^{\lambda_2}$ and $\tau^{\lambda_1}$ be independent exponential random variables with rates $\lambda_2>0$ and $\lambda_1>0$ on a probability space, and let $\tau=\tau^{\lambda_2}\wedge\tau^{\lambda_1}$ be the time until the next payment. Let $r>0$ and let $l_1,l_2$ be natural numbers. Then
--
--   $$E\big[e^{-r\tau}\big]=\frac{\lambda_2+\lambda_1}{\lambda_2+\lambda_1+r}$$
--
--   and the expected discounted opportunity cost of the locked capital until the next payment is
--
--   $$E\Big[\int_0^\tau e^{-rs}\,r(l_1+l_2)\,ds\Big]=(l_1+l_2)\frac{r}{r+\lambda_2+\lambda_1}.$$
--
--   This is the first coefficient of the first-step equation (15) for the cost of a bidirectional channel.
--
--   **Formalization Note** The exponential laws are Mathlib's `expMeasure`, imposed through the push-forward measures of measurable random variables, and independence is `IndepFun`. Expectations are Bochner integrals; the integrability needed for them is part of what is to be proved, not a hypothesis (the stated values are nonzero, so Lean's value $0$ for a non-integrable function cannot make the statement hold).
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 10 (PDF p. 11), proof of Theorem 1, display "the first term equals" (before (15))

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LNChannels.Exact

/-- Proof of Theorem 1, p. 10, "the first term equals": for independent exponential clocks
`τ^{λ₂}`, `τ^{λ₁}` with rates `λ₂`, `λ₁` and `τ = τ^{λ₂} ∧ τ^{λ₁}`,
`E[e^{−rτ}] = (λ₂ + λ₁)/(λ₂ + λ₁ + r)` and
`E[∫₀^τ e^{−rs} r(l₁ + l₂) ds] = (l₁ + l₂) r/(r + λ₂ + λ₁)`. -/
theorem first_term {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ₁ τ₂ : Ω → ℝ) (lam₁ lam₂ r : ℝ) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hr : 0 < r)
    (hτ₁ : Measurable τ₁) (hτ₂ : Measurable τ₂)
    (hlaw₁ : P.map τ₁ = expMeasure lam₁) (hlaw₂ : P.map τ₂ = expMeasure lam₂)
    (hindep : IndepFun τ₂ τ₁ P) (l₁ l₂ : ℕ) :
    ∫ ω, Real.exp (-r * min (τ₂ ω) (τ₁ ω)) ∂P = (lam₂ + lam₁) / (lam₂ + lam₁ + r) ∧
    ∫ ω, (∫ s in (0 : ℝ)..(min (τ₂ ω) (τ₁ ω)), Real.exp (-r * s) * r * ((l₁ : ℝ) + l₂)) ∂P
      = ((l₁ : ℝ) + l₂) * (r / (r + lam₂ + lam₁)) := by sorry

end LNChannels.Exact
