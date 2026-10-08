-- Prove2me | Theorems.Thm_HalfinWhitt81_Stationary_theorem_1
-- name    : HalfinWhitt81.Stationary.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:47:32.785252+00:00
-- url     : https://prove2.me/theorems/c81ff5c2-9b99-435f-a21d-6973ef6f46a7
-- title:
--   Theorem 1 — (Q_n(∞) − n)/√n ⇒ X, exponential above 0 with mass α and truncated normal below 0
-- statement:
--   Consider the sequence of M/M/s queues of Section 2 of Halfin and Whitt (1981): queue $n \ge 1$ has $s_n = n$ servers, service rate $\mu > 0$ and arrival rate $\lambda_n > 0$, with traffic intensity $\rho_n = \lambda_n/(n\mu) < 1$ and $\lambda_n \to \infty$. Let $Q_n(\infty)$ be the stationary number of customers in queue $n$ (waiting or in service). Assume the heavy-traffic condition (2.2),
--   $$\lim_{n\to\infty} (1-\rho_n)\sqrt n = \beta, \qquad \beta > 0,$$
--   and let
--   $$\alpha = \big[1 + \sqrt{2\pi}\,\beta\,\Phi(\beta)\,e^{\beta^2/2}\big]^{-1} = \frac{\varphi(\beta)}{\varphi(\beta) + \beta\Phi(\beta)},$$
--   where $\Phi$ and $\varphi$ are the standard normal distribution function and density. By Proposition 1, $\alpha \in (0,1)$ is the limit of the delay probabilities $P(Q_n(\infty) \ge n)$.
--
--   **Theorem 1.** The scaled stationary queue lengths
--   $$X_n = \frac{Q_n(\infty) - n}{\sqrt n}$$
--   converge in distribution, $X_n \Rightarrow X$, to a random variable $X$ with
--   $$P(X \ge 0) = \alpha, \qquad P(X > x \mid X \ge 0) = e^{-x\beta}\ (x \ge 0), \qquad P(X \le x \mid X \le 0) = \frac{\Phi(\beta + x)}{\Phi(\beta)}\ (x \le 0).$$
--
--   The limit law is a hybrid: an exponential law with rate $\beta$ on $[0,\infty)$ carrying mass $\alpha$, and a normal law truncated at $0$ on $(-\infty,0]$ carrying mass $1-\alpha$. It is the stationary-distribution half of the Halfin–Whitt (quality-and-efficiency-driven) heavy-traffic regime, in which the number of servers grows like the offered load plus a multiple of its square root.
--
--   **Formalization Note** The conclusion asserts the existence of a Borel probability measure $\nu$ on $\mathbb R$ with $\nu([0,\infty)) = \alpha$, $\nu((x,\infty))/\nu([0,\infty)) = e^{-x\beta}$ for every $x \ge 0$, $\nu((-\infty,x])/\nu((-\infty,0]) = \Phi(\beta+x)/\Phi(\beta)$ for every $x \le 0$, and $\sum_k P(Q_n(\infty)=k)\,g((k-n)/\sqrt n) \to \int g\,d\nu$ for every bounded continuous $g:\mathbb R\to\mathbb R$; the last clause is the definition of weak convergence. The page prints (2.13) as $X_n = (Q_n(\infty) - n)n^{1/2}$, a misprint for $n^{-1/2}$ (compare (2.15) and the proof's $\delta_n = n + xn^{1/2}$); the statement uses $n^{-1/2}$. The clause "$x \le 0$" is printed after the third property; the second is read for $x \ge 0$, where it is a conditional probability. $\alpha$ is written as the closed form (2.3), equal under (2.2) to the limit in (2.1) by Proposition 1. Hypotheses on queue $n$ are imposed for $n \ge 1$; the page's $\lambda_n \to \infty$ is kept although it follows from (2.2).
-- source:
--   Halfin and Whitt, Heavy-Traffic Limits for Queues with Many Exponential Servers, Operations Research 29 (1981), p. 576, Theorem 1 (with (2.13), corrected to n^{−1/2}, and (2.2)–(2.3), p. 574)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang
import Definitions.Def_HalfinWhitt81_Stationary_Basic

namespace HalfinWhitt81.Stationary

open Filter Topology MeasureTheory QueueingFundamentals.BirthDeath

/-- Halfin–Whitt (1981), Theorem 1, p. 576. For the sequence of `M/M/n` queues of §2 under (2.2),
`(1 − ρ_n)√n → β > 0`, with `α = φ(β)/(φ(β) + βΦ(β))` (the limit (2.3) of the delay
probabilities), the scaled stationary queue length `X_n = (Q_n(∞) − n)/√n` converges weakly to a
law `X` with `P(X ≥ 0) = α`, `P(X > x | X ≥ 0) = e^{−xβ}` for `x ≥ 0`, and
`P(X ≤ x | X ≤ 0) = Φ(β + x)/Φ(β)` for `x ≤ 0`. Weak convergence: `E g(X_n) → E g(X)` for every
bounded continuous `g : ℝ → ℝ`. -/
theorem theorem_1
    (μ : ℝ) (hμ : 0 < μ) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n ∧ lam n < n * μ)
    (hlam_top : Tendsto lam atTop atTop)
    (p : ℕ → ℕ → ℝ)
    (hp : ∀ n : ℕ, 1 ≤ n → IsSteadyState (fun _ => lam n) (mmcDeath μ n) (p n))
    (β : ℝ) (hβ : 0 < β)
    (hβlim : Tendsto (fun n : ℕ => (1 - lam n / (n * μ)) * Real.sqrt n) atTop (𝓝 β)) :
    ∃ ν : ProbabilityMeasure ℝ,
      (ν : Measure ℝ).real (Set.Ici 0) = halfinWhittAlpha β ∧
      (∀ x : ℝ, 0 ≤ x →
        (ν : Measure ℝ).real (Set.Ioi x) / (ν : Measure ℝ).real (Set.Ici 0) =
          Real.exp (-(x * β))) ∧
      (∀ x : ℝ, x ≤ 0 →
        (ν : Measure ℝ).real (Set.Iic x) / (ν : Measure ℝ).real (Set.Iic 0) =
          ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (β + x) /
            ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) β) ∧
      ∀ g : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => scaledExpect (p n) n g) atTop (𝓝 (∫ x, g x ∂(ν : Measure ℝ))) := by sorry

end HalfinWhitt81.Stationary
