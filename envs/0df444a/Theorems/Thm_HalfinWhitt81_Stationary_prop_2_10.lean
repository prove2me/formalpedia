-- Prove2me | Theorems.Thm_HalfinWhitt81_Stationary_prop_2_10
-- name    : HalfinWhitt81.Stationary.prop_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:47:18.109815+00:00
-- url     : https://prove2.me/theorems/63e0de88-2624-4bbb-ae2c-3ada1ca34494
-- title:
--   Proposition 2(i), (2.10) — √n P(Q_n(∞) = [δ_n] | Q_n(∞) ≤ n) → φ(β − δ)/Φ(β)
-- statement:
--   Consider the sequence of M/M/s queues of Section 2 of Halfin and Whitt (1981): queue $n \ge 1$ has $n$ servers, service rate $\mu > 0$, arrival rate $\lambda_n > 0$ with $\rho_n = \lambda_n/(n\mu) < 1$ and $\lambda_n \to \infty$, and stationary queue length $Q_n(\infty)$. Assume (2.2), $(1-\rho_n)\sqrt n \to \beta > 0$. Let $\Phi$ and $\varphi$ be the standard normal distribution function and density, $\delta > 0$, and let $[x]$ be the greatest integer less than or equal to $x$.
--
--   If $\{\delta_n\}$ is a sequence of real constants with $\delta_n \le n$ for all $n$ and $(n-\delta_n)n^{-1/2} \to \delta$, then
--   $$\lim_{n\to\infty} \sqrt n \, P\big(Q_n(\infty) = [\delta_n] \,\big|\, Q_n(\infty) \le n\big) = \frac{\varphi(\beta-\delta)}{\Phi(\beta)} .$$
--
--   This is the local (density) form of (2.9): the conditional probability of a single state at scaled distance $\delta$ below $n$ is $n^{-1/2}$ times the truncated normal density.
--
--   **Formalization Note** Since $[\delta_n] \le \delta_n \le n$, the conditional probability is $P(Q_n(\infty) = [\delta_n])/P(Q_n(\infty) \le n)$. $[x]$ is `Int.floor`, and $P(Q_n(\infty) = m) = 0$ for a negative integer $m$ (possible only for finitely many $n$). The conditioning event is the printed $Q_n(\infty) \le n$. Hypotheses are imposed for $n \ge 1$, and (2.2) is the standing assumption of Section 2; $\lambda_n \to \infty$ is kept although it follows from (2.2).
-- source:
--   Halfin and Whitt, Heavy-Traffic Limits for Queues with Many Exponential Servers, Operations Research 29 (1981), p. 576, Proposition 2(i), (2.10)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_HalfinWhitt81_Stationary_Basic

namespace HalfinWhitt81.Stationary

open Filter Topology QueueingFundamentals.BirthDeath

/-- Halfin–Whitt (1981), Proposition 2(i), (2.10), p. 576. Same setting and hypotheses as (2.9):
for `δ > 0` and every real sequence `δ_n ≤ n` with `(n − δ_n)/√n → δ`,
`√n · P(Q_n(∞) = [δ_n] | Q_n(∞) ≤ n) → φ(β − δ)/Φ(β)`, where `[x] = ⌊x⌋` is the greatest integer
`≤ x`. Since `[δ_n] ≤ δ_n ≤ n`, the conditional probability is
`P(Q_n(∞) = [δ_n])/P(Q_n(∞) ≤ n)` (and `P(Q_n(∞) = m) = 0` for a negative integer `m`). -/
theorem prop_2_10
    (μ : ℝ) (hμ : 0 < μ) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n ∧ lam n < n * μ)
    (hlam_top : Tendsto lam atTop atTop)
    (p : ℕ → ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → IsSteadyState (fun _ => lam n) (mmcDeath μ n) (p n))
    (β : ℝ) (hβ : 0 < β)
    (hβlim : Tendsto (fun n : ℕ => (1 - lam n / (n * μ)) * Real.sqrt n) atTop (𝓝 β))
    (δ : ℝ) (hδ : 0 < δ) (d : ℕ → ℝ) (hd : ∀ n : ℕ, 1 ≤ n → d n ≤ n)
    (hdlim : Tendsto (fun n : ℕ => ((n : ℝ) - d n) / Real.sqrt n) atTop (𝓝 δ)) :
    Tendsto (fun n : ℕ => Real.sqrt n * probEqInt (p n) ⌊d n⌋ / probLE (p n) n) atTop
      (𝓝 (ProbabilityTheory.gaussianPDFReal 0 1 (β - δ) /
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) β)) := by sorry

end HalfinWhitt81.Stationary
