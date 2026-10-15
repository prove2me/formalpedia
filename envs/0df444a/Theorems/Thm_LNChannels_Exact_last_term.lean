-- Prove2me | Theorems.Thm_LNChannels_Exact_last_term
-- name    : LNChannels.Exact.last_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:23.211667+00:00
-- url     : https://prove2.me/theorems/2cec35be-a41c-4fff-9eee-ab492da5d7b1
-- title:
--   Proof of Theorem 1, p. 10 — the discounted residual cost after the next payment
-- statement:
--   Let $\tau^{\lambda_2}$ and $\tau^{\lambda_1}$ be independent exponential random variables with rates $\lambda_2>0$ and $\lambda_1>0$, let $\tau=\tau^{\lambda_2}\wedge\tau^{\lambda_1}$ and $r>0$. Starting from balance $n\in\mathbb Z$, the balance after the next payment is $n+1$ if $\tau^{\lambda_2}$ rings first (node 2 pays) and $n-1$ otherwise. Then for every function $J:\mathbb Z\to\mathbb R$,
--
--   $$E\big[e^{-r\tau}J(X_{t+\tau})\mid X_t=n\big]=J(n+1)\frac{\lambda_2}{r+\lambda_2+\lambda_1}+J(n-1)\frac{\lambda_1}{r+\lambda_2+\lambda_1}.$$
--
--   These are the second and third coefficients of the first-step equation (15).
--
--   **Formalization Note** The conditional expectation given $X_t=n$ is written as the unconditional expectation of $e^{-r\tau}J(n\pm1)$, where the sign is chosen by the event $\{\tau^{\lambda_2}<\tau^{\lambda_1}\}$; a tie $\tau^{\lambda_2}=\tau^{\lambda_1}$ is sent to $n-1$ and has probability zero. The paper factors the expectation as $E[e^{-r\tau}]\,P(\tau=\tau^{\lambda_2})$; the statement is the joint expectation, and no independence of $\tau$ from the identity of the first clock is assumed. Laws are `expMeasure` via push-forwards, independence is `IndepFun`, and integrability is part of what is to be proved.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 10 (PDF p. 11), proof of Theorem 1, display "the last term equals" (before (15))

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LNChannels.Exact

/-- Proof of Theorem 1, p. 10, "the last term equals": for independent exponential clocks
`τ^{λ₂}`, `τ^{λ₁}` and `τ = τ^{λ₂} ∧ τ^{λ₁}`, the balance moves from `n` to `n + 1` if
`τ^{λ₂}` rings first and to `n − 1` otherwise, and for every `J : ℤ → ℝ`
`E[e^{−rτ} J(X_{t+τ}) | X_t = n] = J(n + 1) λ₂/(r + λ₂ + λ₁) + J(n − 1) λ₁/(r + λ₂ + λ₁)`. -/
theorem last_term {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ₁ τ₂ : Ω → ℝ) (lam₁ lam₂ r : ℝ) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hr : 0 < r)
    (hτ₁ : Measurable τ₁) (hτ₂ : Measurable τ₂)
    (hlaw₁ : P.map τ₁ = expMeasure lam₁) (hlaw₂ : P.map τ₂ = expMeasure lam₂)
    (hindep : IndepFun τ₂ τ₁ P) (J : ℤ → ℝ) (n : ℤ) :
    ∫ ω, Real.exp (-r * min (τ₂ ω) (τ₁ ω)) * J (if τ₂ ω < τ₁ ω then n + 1 else n - 1) ∂P
      = J (n + 1) * (lam₂ / (r + lam₂ + lam₁))
        + J (n - 1) * (lam₁ / (r + lam₂ + lam₁)) := by sorry

end LNChannels.Exact
