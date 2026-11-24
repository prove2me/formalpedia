-- Prove2me | Theorems.Thm_HalfinWhitt81_Stationary_Supplement_theorem_3
-- name    : HalfinWhitt81.Stationary.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:50:23.262791+00:00
-- url     : https://prove2.me/theorems/423d0a06-dc61-4b87-8b22-b99d43b6e641
-- title:
--   Theorem 3 — the scaled GI/M/n queue process converges in D[0, ∞) to a diffusion with variance μ(1 + c²)
-- statement:
--   Fix $\mu>0$, $\beta>0$ and a real $c^2$. For each $n\ge1$ let $Q_n$ be the number in system of a $GI/M/n$ queue (see the Section 3 model): $n$ servers, exponential services of rate $\mu$, i.i.d. nonnegative interarrival times distributed as $u_n$ (the law may change with $n$), an arrival at time $0$, and an arbitrary prearrival number independent of the arrival and service primitives; all queues live on one probability space. Let $\lambda_n$ satisfy $0<\lambda_n<n\mu$, so that $\rho_n=\lambda_n/(n\mu)<1$. Assume (2.2), $(1-\rho_n)\sqrt n\to\beta$, and (3.1):
--
--   1. $E u_n=\lambda_n^{-1}$ for every $n\ge1$;
--   2. $\lim_{n\to\infty}\lambda_n^2\operatorname{Var}u_n=c^2$;
--   3. $\sup_{n\ge1}\lambda_n^3E u_n^3<\infty$.
--
--   Let $Y_n(t)=(Q_n(t)-n)/\sqrt n$. If $Y_n(0)\Rightarrow\nu$ for a probability law $\nu$ on $\mathbb R$, then there is a diffusion $Y^*$ with $Y^*(0)\sim\nu$, drift and infinitesimal variance
--
--   $$m(x)=\begin{cases}-\mu\beta,&x\ge0,\\-\mu(x+\beta),&x<0,\end{cases}\qquad\sigma^2(x)=\mu(1+c^2),$$
--
--   such that $Y_n\Rightarrow Y^*$ in $D[0,\infty)$ with the $J_1$ topology.
--
--   The theorem shows that renewal arrivals change the Halfin–Whitt limit only through the variance of the interarrival times: the drift is that of Theorem 2, and the noise variance changes from $2\mu$ to $\mu(1+c^2)$; Poisson arrivals ($c^2=1$) recover Theorem 2.
--
--   **Formalization Note** The limit is the Section 3 predicate `IsGIDiffusionSolution`: $Y^*(t)=Y^*(0)-\mu\int_0^t(\beta+\min(Y^*(u),0))du+\sqrt{\mu(1+c^2)}B(t)$, written as the published Theorem 2 equation for $Y^*/s$, $s=\sqrt{(1+c^2)/2}$, with $\beta/s$ in place of $\beta$. Process convergence is the published `CouplingConverges`, equivalent to $J_1$ weak convergence for continuous limits. Condition (iii) is stated with $u_n\in L^3$ (finiteness of $Eu_n^3$, which (iii) asserts) and a uniform bound on $\lambda_n^3Eu_n^3$. $c^2\ge0$ is not assumed: it follows from (ii).
--
--   Differences from the source:
--
--   - encoding: Y_n ⇒ Y* in D[0,∞) with the J₁ topology → CouplingConverges (Skorokhod coupling, a.s. uniform convergence on compacts); reason: equivalent because the limit diffusion has continuous paths
--   - encoding: the sequence of GI/M/n queues, each on its own space → all queues on one probability space; reason: weak convergence depends only on the laws, and any family of laws is realized on a product space
--   - reading: Y* is a diffusion process with m(x), σ²(x) = μ(1+c²) → Y*/s solves the published Theorem 2 equation with parameter β/s, s = √((1+c²)/2), i.e. Y*(t) = Y*(0) + ∫₀ᵗ m(Y*(u)) du + √(μ(1+c²)) B(t); reason: the generator (2.16) with this m and σ² is that of the equation; dividing by s turns σ² = μ(1+c²) into 2μ and the drift into −μ(β/s + min(x,0))
--   - reading: an arrival occurs at time 0; Y_n(0) → Q_n(0) is the right-continuous state after the initial batch; q0 is the independent prearrival state; reason: under (3.1), E(λ_n u_n)=1 and uniformly bounded E(λ_n u_n)^3 bound P(u_n>0) away from zero by Hölder; the geometric initial batch is uniformly tight, hence divided by √n tends to zero in probability
--   - reading: GI/M/s queue → Q(t) = q0 + 1 + A(t) − S(μ∫₀ᵗ min(Q,n)), where q0 is the prearrival initial number, independent of the i.i.d. nonnegative interarrivals and unit Poisson clock S; reason: the arrival at zero and all subsequent arrivals, including simultaneous arrivals when u=0, are counted; the independent initial state is before that batch
--   - encoding: (3.1)(iii) sup_{n≥1} λ_n³ E u_n³ < ∞ → E|u_n|³ < ∞ for n ≥ 1 and ∃K, λ_n³ E u_n³ ≤ K for n ≥ 1; reason: (iii) asserts finiteness of E u_n³; Lean's integral of a non-integrable function would otherwise be 0
--   - reading: the setup "as before" (λ_n → ∞) → not stated; reason: it follows from (2.2)
-- source:
--   Halfin and Whitt, Heavy-Traffic Limits for Queues with Many Exponential Servers, Operations Research 29 (1981), p. 580, Theorem 3 (with Section 3 setup and (3.1), p. 579)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_HalfinWhitt81_Stationary_Supplement_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace HalfinWhitt81.Stationary.Supplement

open BellWilliams2001.ThresholdPolicy ErlangA.Diffusion

/-- Halfin–Whitt (1981), Theorem 3, p. 580. For `n ≥ 1` let `Q_n` be a `GI/M/n` queue with
service rate `μ > 0`, interarrival times `u_n` (law depending on `n`), arrival rate `λ_n`,
`0 < λ_n < nμ`, an arrival at time `0`, all systems on one probability space. Assume (2.2):
`(1 − λ_n/(nμ))√n → β > 0`, and (3.1): `E u_n = 1/λ_n`, `λ_n² Var u_n → c²`,
`sup_{n ≥ 1} λ_n³ E u_n³ < ∞`. If `Y_n(0) = (Q_n(0) − n)/√n ⇒ ν`, then there is a diffusion `Y*`
with drift `−μβ` on `x ≥ 0`, `−μ(x + β)` on `x < 0` and infinitesimal variance `μ(1 + c²)`,
started from `ν`, with `Y_n ⇒ Y*` in `D[0, ∞)` (coupling form `CouplingConverges`). -/
theorem theorem_3 (μ β c2 : ℝ) (hμ : 0 < μ) (hβ : 0 < β) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n ∧ lam n < n * μ)
    (hβlim : Tendsto (fun n : ℕ => (1 - lam n / (n * μ)) * Real.sqrt n) atTop (𝓝 β))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u : ℕ → ℕ → Ω → ℝ) (S : ℕ → Ω → ℝ → ℝ) (q0 : ℕ → Ω → ℕ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsGIMnSystem P n μ (u n) (S n) (q0 n) (Q n))
    (hL3 : ∀ n : ℕ, 1 ≤ n → MemLp (u n 1) 3 P)
    (hmean : ∀ n : ℕ, 1 ≤ n → ∫ ω, u n 1 ω ∂P = 1 / lam n)
    (hvar : Tendsto (fun n : ℕ => lam n ^ 2 * variance (u n 1) P) atTop (𝓝 c2))
    (hthird : ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → lam n ^ 3 * ∫ ω, u n 1 ω ^ 3 ∂P ≤ K)
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (scaled n (Q n) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (b : ℝ≥0 → Ω' → ℝ)
        (Y : Ω' → ℝ → ℝ),
        IsGIDiffusionSolution P' μ β c2 (ν : Measure ℝ) b Y ∧
        CouplingConverges P P' (fun n => scaled n (Q n)) (fun ω t (_ : Fin 1) => Y ω t) := by sorry

end HalfinWhitt81.Stationary.Supplement
