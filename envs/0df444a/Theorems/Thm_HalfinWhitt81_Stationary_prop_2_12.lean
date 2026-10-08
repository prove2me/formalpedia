-- Prove2me | Theorems.Thm_HalfinWhitt81_Stationary_prop_2_12
-- name    : HalfinWhitt81.Stationary.prop_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:47:44.960091+00:00
-- url     : https://prove2.me/theorems/d048f3fe-766c-4e9d-b0df-b46c683d8d32
-- title:
--   Proposition 2(ii), (2.12) — √n P(Q_n(∞) = [δ_n] | Q_n(∞) ≥ n) → βe^{−δβ}
-- statement:
--   Consider the sequence of M/M/s queues of Section 2 of Halfin and Whitt (1981): queue $n \ge 1$ has $n$ servers, service rate $\mu > 0$, arrival rate $\lambda_n > 0$ with $\rho_n = \lambda_n/(n\mu) < 1$ and $\lambda_n \to \infty$, and stationary queue length $Q_n(\infty)$. Assume (2.2), $(1-\rho_n)\sqrt n \to \beta > 0$. Let $\delta > 0$ and let $[x]$ be the greatest integer less than or equal to $x$.
--
--   If $\{\delta_n\}$ is a sequence of real constants with $\delta_n \ge n$ for all $n$ and $(\delta_n - n)n^{-1/2} \to \delta$, then
--   $$\lim_{n\to\infty} \sqrt n \, P\big(Q_n(\infty) = [\delta_n] \,\big|\, Q_n(\infty) \ge n\big) = \beta e^{-\delta\beta} .$$
--
--   This is the local form of (2.11): the limit is the exponential density with rate $\beta$ at $\delta$.
--
--   **Formalization Note** The page prints the limit as $\beta e^{-\beta}$. That is a misprint for $\beta e^{-\delta\beta}$: given $Q_n(\infty) \ge n$, $Q_n(\infty) - n$ is geometric with ratio $\rho_n$, so the left side is $\sqrt n(1-\rho_n)\rho_n^{[\delta_n]-n}$, whose limit depends on $\delta$; the corrected value is also the density of the exponential limit of (2.11) and the density $\alpha\beta e^{-\beta x}$ behind Theorem 1. The statement formalizes $\beta e^{-\delta\beta}$. Since $[\delta_n] \ge n$, the conditional probability is $P(Q_n(\infty) = [\delta_n])/P(Q_n(\infty) \ge n)$; $[x]$ is `Int.floor`. Hypotheses are imposed for $n \ge 1$, (2.2) is the standing assumption of Section 2, and $\lambda_n \to \infty$ is kept although it follows from (2.2).
-- source:
--   Halfin and Whitt, Heavy-Traffic Limits for Queues with Many Exponential Servers, Operations Research 29 (1981), p. 576, Proposition 2(ii), (2.12) (printed limit βe^{−β} corrected to βe^{−δβ})

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_HalfinWhitt81_Stationary_Basic

namespace HalfinWhitt81.Stationary

open Filter Topology QueueingFundamentals.BirthDeath

/-- Halfin–Whitt (1981), Proposition 2(ii), (2.12), p. 576, with the printed limit `βe^{−β}`
corrected to `βe^{−δβ}`. Same setting and hypotheses as (2.11): for `δ > 0` and every real
sequence `δ_n ≥ n` with `(δ_n − n)/√n → δ`,
`√n · P(Q_n(∞) = [δ_n] | Q_n(∞) ≥ n) → βe^{−δβ}`, where `[x] = ⌊x⌋`. Since `[δ_n] ≥ n`, the
conditional probability is `P(Q_n(∞) = [δ_n])/P(Q_n(∞) ≥ n)`. -/
theorem prop_2_12
    (μ : ℝ) (hμ : 0 < μ) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n ∧ lam n < n * μ)
    (hlam_top : Tendsto lam atTop atTop)
    (p : ℕ → ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → IsSteadyState (fun _ => lam n) (mmcDeath μ n) (p n))
    (β : ℝ) (hβ : 0 < β)
    (hβlim : Tendsto (fun n : ℕ => (1 - lam n / (n * μ)) * Real.sqrt n) atTop (𝓝 β))
    (δ : ℝ) (hδ : 0 < δ) (d : ℕ → ℝ) (hd : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ d n)
    (hdlim : Tendsto (fun n : ℕ => (d n - n) / Real.sqrt n) atTop (𝓝 δ)) :
    Tendsto (fun n : ℕ => Real.sqrt n * probEqInt (p n) ⌊d n⌋ / probGE (p n) n) atTop
      (𝓝 (β * Real.exp (-(δ * β)))) := by sorry

end HalfinWhitt81.Stationary
