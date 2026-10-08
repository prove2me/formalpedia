-- Prove2me | Theorems.Thm_HalfinWhitt81_Stationary_prop_2_11
-- name    : HalfinWhitt81.Stationary.prop_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:47:43.5238+00:00
-- url     : https://prove2.me/theorems/10dcebc9-f865-4a09-8a5e-4617d7b49b26
-- title:
--   Proposition 2(ii), (2.11) — P(Q_n(∞) ≥ δ_n | Q_n(∞) ≥ n) → e^{−δβ}
-- statement:
--   Consider the sequence of M/M/s queues of Section 2 of Halfin and Whitt (1981): queue $n \ge 1$ has $n$ servers, service rate $\mu > 0$, arrival rate $\lambda_n > 0$ with $\rho_n = \lambda_n/(n\mu) < 1$ and $\lambda_n \to \infty$, and stationary queue length $Q_n(\infty)$. Assume (2.2), $(1-\rho_n)\sqrt n \to \beta > 0$, and let $\delta > 0$.
--
--   If $\{\delta_n\}$ is a sequence of real constants with $\delta_n \ge n$ for all $n$ and $(\delta_n - n)n^{-1/2} \to \delta$, then
--   $$\lim_{n\to\infty} P\big(Q_n(\infty) \ge \delta_n \,\big|\, Q_n(\infty) \ge n\big) = e^{-\delta\beta} .$$
--
--   Given that all servers are busy, the scaled excess $(Q_n(\infty) - n)/\sqrt n$ is asymptotically exponential with rate $\beta$. This is the upper half of Theorem 1.
--
--   **Formalization Note** Since $\delta_n \ge n$, the conditional probability is the ratio $P(Q_n(\infty) \ge \delta_n)/P(Q_n(\infty) \ge n)$; the denominator is the delay probability $\alpha_n$, which is positive. Hypotheses are imposed for $n \ge 1$, and (2.2) is the standing assumption of Section 2; $\lambda_n \to \infty$ is kept although it follows from (2.2).
-- source:
--   Halfin and Whitt, Heavy-Traffic Limits for Queues with Many Exponential Servers, Operations Research 29 (1981), p. 576, Proposition 2(ii), (2.11)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_HalfinWhitt81_Stationary_Basic

namespace HalfinWhitt81.Stationary

open Filter Topology QueueingFundamentals.BirthDeath

/-- Halfin–Whitt (1981), Proposition 2(ii), (2.11), p. 576. Same setting as (2.9): for `δ > 0` and
every real sequence `δ_n ≥ n` with `(δ_n − n)/√n → δ`,
`P(Q_n(∞) ≥ δ_n | Q_n(∞) ≥ n) → e^{−δβ}`. Since `δ_n ≥ n`, the conditional probability is
`P(Q_n(∞) ≥ δ_n)/P(Q_n(∞) ≥ n)`. -/
theorem prop_2_11
    (μ : ℝ) (hμ : 0 < μ) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n ∧ lam n < n * μ)
    (hlam_top : Tendsto lam atTop atTop)
    (p : ℕ → ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → IsSteadyState (fun _ => lam n) (mmcDeath μ n) (p n))
    (β : ℝ) (hβ : 0 < β)
    (hβlim : Tendsto (fun n : ℕ => (1 - lam n / (n * μ)) * Real.sqrt n) atTop (𝓝 β))
    (δ : ℝ) (hδ : 0 < δ) (d : ℕ → ℝ) (hd : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ d n)
    (hdlim : Tendsto (fun n : ℕ => (d n - n) / Real.sqrt n) atTop (𝓝 δ)) :
    Tendsto (fun n : ℕ => probGE (p n) (d n) / probGE (p n) n) atTop
      (𝓝 (Real.exp (-(δ * β)))) := by sorry

end HalfinWhitt81.Stationary
