-- Prove2me | Theorems.Thm_HalfinWhitt81_Stationary_prop_2_9
-- name    : HalfinWhitt81.Stationary.prop_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:47:10.076674+00:00
-- url     : https://prove2.me/theorems/52ed24ed-3bff-4aa3-af0b-b63424f600ac
-- title:
--   Proposition 2(i), (2.9) — P(Q_n(∞) ≤ δ_n | Q_n(∞) ≤ n) → Φ(β − δ)/Φ(β)
-- statement:
--   Consider the sequence of M/M/s queues of Section 2 of Halfin and Whitt (1981): queue $n \ge 1$ has $s_n = n$ servers, service rate $\mu > 0$ and arrival rate $\lambda_n > 0$, with traffic intensity $\rho_n = \lambda_n/(n\mu) < 1$ and $\lambda_n \to \infty$. Let $Q_n(\infty)$ have the stationary distribution $p_n$ of queue $n$. Assume the heavy-traffic condition (2.2),
--   $$\lim_{n\to\infty} (1-\rho_n)\sqrt n = \beta, \qquad \beta > 0 .$$
--   Let $\Phi$ and $\varphi$ be the standard normal distribution function and density, and let $\delta > 0$.
--
--   If $\{\delta_n\}$ is a sequence of real constants with $\delta_n \le n$ for all $n$ and $(n - \delta_n)n^{-1/2} \to \delta$, then
--   $$\lim_{n\to\infty} P\big(Q_n(\infty) \le \delta_n \,\big|\, Q_n(\infty) \le n\big) = \frac{\Phi(\beta-\delta)}{\Phi(\beta)} .$$
--
--   Below the number of servers, the queue length sits at distance of order $\sqrt n$ below $n$ and, conditioned on not all servers being busy, its scaled deficit has a normal law truncated at $\beta$. This is the lower half of Theorem 1.
--
--   **Formalization Note** "For the rest of this section we assume (2.1) or, equivalently, (2.2)" (p. 575) is the hypothesis (2.2); its equivalence with (2.1) is Proposition 1. Since $\delta_n \le n$, the conditional probability is the ratio $P(Q_n(\infty) \le \delta_n)/P(Q_n(\infty) \le n)$, whose denominator is positive. Hypotheses on the $n$-th queue and on $\delta_n$ are imposed for $n \ge 1$; only the limit is asserted. The page's $\lambda_n \to \infty$ is kept as a hypothesis although it follows from (2.2).
-- source:
--   Halfin and Whitt, Heavy-Traffic Limits for Queues with Many Exponential Servers, Operations Research 29 (1981), p. 575, Proposition 2(i), (2.9)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_HalfinWhitt81_Stationary_Basic

namespace HalfinWhitt81.Stationary

open Filter Topology QueueingFundamentals.BirthDeath

/-- Halfin–Whitt (1981), Proposition 2(i), (2.9), p. 575. For the sequence of `M/M/n` queues of
§2 (queue `n` has `n` servers, service rate `μ`, arrival rate `λ_n` with `ρ_n = λ_n/(nμ) < 1`,
`λ_n → ∞`, stationary law `p n`) under (2.2), `(1 − ρ_n)√n → β > 0`: for `δ > 0` and every real
sequence `δ_n ≤ n` with `(n − δ_n)/√n → δ`,
`P(Q_n(∞) ≤ δ_n | Q_n(∞) ≤ n) → Φ(β − δ)/Φ(β)`. Since `δ_n ≤ n`, the conditional probability is
`P(Q_n(∞) ≤ δ_n)/P(Q_n(∞) ≤ n)`. -/
theorem prop_2_9
    (μ : ℝ) (hμ : 0 < μ) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n ∧ lam n < n * μ)
    (hlam_top : Tendsto lam atTop atTop)
    (p : ℕ → ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → IsSteadyState (fun _ => lam n) (mmcDeath μ n) (p n))
    (β : ℝ) (hβ : 0 < β)
    (hβlim : Tendsto (fun n : ℕ => (1 - lam n / (n * μ)) * Real.sqrt n) atTop (𝓝 β))
    (δ : ℝ) (hδ : 0 < δ) (d : ℕ → ℝ) (hd : ∀ n : ℕ, 1 ≤ n → d n ≤ n)
    (hdlim : Tendsto (fun n : ℕ => ((n : ℝ) - d n) / Real.sqrt n) atTop (𝓝 δ)) :
    Tendsto (fun n : ℕ => probLE (p n) (d n) / probLE (p n) n) atTop
      (𝓝 (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (β - δ) /
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) β)) := by sorry

end HalfinWhitt81.Stationary
