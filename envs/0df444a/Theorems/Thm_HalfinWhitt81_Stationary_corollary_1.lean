-- Prove2me | Theorems.Thm_HalfinWhitt81_Stationary_corollary_1
-- name    : HalfinWhitt81.Stationary.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:05:33.194167+00:00
-- url     : https://prove2.me/theorems/5201a4b9-4e29-484b-b775-dbfd7d84f0be
-- title:
--   Corollary 1, (2.14) — the first four moments and the variance of X_n converge
-- statement:
--   Consider the sequence of M/M/s queues of Section 2 of Halfin and Whitt (1981): queue $n \ge 1$ has $n$ servers, service rate $\mu > 0$, arrival rate $\lambda_n > 0$ with $\rho_n = \lambda_n/(n\mu) < 1$ and $\lambda_n \to \infty$, and stationary queue length $Q_n(\infty)$. Assume (2.2), $(1-\rho_n)\sqrt n \to \beta > 0$, let $\alpha = \varphi(\beta)/(\varphi(\beta) + \beta\Phi(\beta))$ be the limit (2.3) of the delay probabilities, and let $X_n = (Q_n(\infty) - n)/\sqrt n$.
--
--   Then every moment $E X_n^j = \sum_{k \ge 0} P(Q_n(\infty) = k)\,((k-n)/\sqrt n)^j$ is a convergent series, and as $n \to \infty$
--
--   1. $E X_n \to -\beta + \alpha\beta^{-1}$,
--   2. $E X_n^2 \to \beta^2 + 2\alpha\beta^{-2} + (1-\alpha)$,
--   3. $E X_n^3 \to -\beta^3 - (3-\alpha)\beta + 6\alpha\beta^{-3}$,
--   4. $E X_n^4 \to \beta^4 + (6-\alpha)\beta^2 + 3(1-\alpha) + 24\alpha\beta^{-4}$,
--   5. $\operatorname{Var} X_n \to (1+\alpha) + (2\alpha-\alpha^2)\beta^{-2}$.
--
--   The limits are the moments of the limit $X$ of Theorem 1, so the approximations of Section 5 can use them for the mean and variance of the number in system.
--
--   **Formalization Note** The paper writes "$EX_n^k \to EX^k = \dots$"; the statement asserts the convergence to the displayed explicit values (that these are the moments of $X$ is not part of it). $\operatorname{Var} X_n$ is $E X_n^2 - (E X_n)^2$. The convergence of the moment series is part of the conclusion. (2.13) is used with the corrected scaling $n^{-1/2}$; hypotheses are imposed for $n \ge 1$, and $\lambda_n \to \infty$ is kept although it follows from (2.2).
-- source:
--   Halfin and Whitt, Heavy-Traffic Limits for Queues with Many Exponential Servers, Operations Research 29 (1981), p. 577, Corollary 1, (2.14)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang
import Definitions.Def_HalfinWhitt81_Stationary_Basic

namespace HalfinWhitt81.Stationary

open Filter Topology QueueingFundamentals.BirthDeath

/-- Halfin–Whitt (1981), Corollary 1, (2.14), p. 577. For the sequence of `M/M/n` queues of §2 under
(2.2), `(1 − ρ_n)√n → β > 0`, with `α = φ(β)/(φ(β) + βΦ(β))` and `X_n = (Q_n(∞) − n)/√n`: every
moment series `E X_n^j = ∑_k p_n(k) ((k − n)/√n)^j` converges (`n ≥ 1`), and
(i) `E X_n → −β + αβ⁻¹`, (ii) `E X_n² → β² + 2αβ⁻² + (1 − α)`,
(iii) `E X_n³ → −β³ − (3 − α)β + 6αβ⁻³`, (iv) `E X_n⁴ → β⁴ + (6 − α)β² + 3(1 − α) + 24αβ⁻⁴`,
(v) `Var X_n = E X_n² − (E X_n)² → (1 + α) + (2α − α²)β⁻²`. -/
theorem corollary_1
    (μ : ℝ) (hμ : 0 < μ) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n ∧ lam n < n * μ)
    (hlam_top : Tendsto lam atTop atTop)
    (p : ℕ → ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → IsSteadyState (fun _ => lam n) (mmcDeath μ n) (p n))
    (β : ℝ) (hβ : 0 < β)
    (hβlim : Tendsto (fun n : ℕ => (1 - lam n / (n * μ)) * Real.sqrt n) atTop (𝓝 β)) :
    let α : ℝ := halfinWhittAlpha β
    let M : ℕ → ℕ → ℝ := fun j n => scaledExpect (p n) n (fun x => x ^ j)
    (∀ n : ℕ, 1 ≤ n → ∀ j : ℕ,
      Summable (fun k : ℕ => p n k * (((k : ℝ) - n) / Real.sqrt n) ^ j)) ∧
    Tendsto (M 1) atTop (𝓝 (-β + α * β⁻¹)) ∧
    Tendsto (M 2) atTop (𝓝 (β ^ 2 + 2 * α * β⁻¹ ^ 2 + (1 - α))) ∧
    Tendsto (M 3) atTop (𝓝 (-β ^ 3 - (3 - α) * β + 6 * α * β⁻¹ ^ 3)) ∧
    Tendsto (M 4) atTop
      (𝓝 (β ^ 4 + (6 - α) * β ^ 2 + 3 * (1 - α) + 24 * α * β⁻¹ ^ 4)) ∧
    Tendsto (fun n => M 2 n - M 1 n ^ 2) atTop
      (𝓝 ((1 + α) + (2 * α - α ^ 2) * β⁻¹ ^ 2)) := by sorry

end HalfinWhitt81.Stationary
