-- Prove2me | Theorems.Thm_HalfinWhitt81_Stationary_Supplement_theorem_2
-- name    : HalfinWhitt81.Stationary.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:49:37.905799+00:00
-- url     : https://prove2.me/theorems/3ed59acc-5b06-4570-a257-4df625c6dff7
-- title:
--   Theorem 2 — the scaled M/M/n queue process converges in D[0, ∞) to the Halfin–Whitt diffusion
-- statement:
--   Fix $\mu>0$ and $\beta>0$. For each $n\ge1$ let $Q_n=\{Q_n(t),t\ge0\}$ be the number of customers in an $M/M/n$ queue with Poisson arrivals of rate $\lambda_n$, $0<\lambda_n<n\mu$, exponential services of rate $\mu$, and an arbitrary initial number in system $Q_n(0)$ independent of the arrival and service processes; all the queues live on one probability space. Assume the heavy-traffic condition (2.2),
--
--   $$\lim_{n\to\infty}\Big(1-\frac{\lambda_n}{n\mu}\Big)\sqrt n=\beta .$$
--
--   Form the normalized processes $Y_n(t)=(Q_n(t)-n)/\sqrt n$. If $Y_n(0)\Rightarrow\nu$ for a probability law $\nu$ on $\mathbb R$, then there is a diffusion $Y$ with $Y(0)\sim\nu$, drift and infinitesimal variance
--
--   $$m(x)=\begin{cases}-\mu\beta,&x\ge0,\\-\mu(x+\beta),&x\le0,\end{cases}\qquad \sigma^2(x)=2\mu,$$
--
--   such that $Y_n\Rightarrow Y$ in $D[0,\infty)$ with the Skorokhod $J_1$ topology.
--
--   This is the process-level counterpart of Theorem 1: it describes the whole time evolution of the queue in the Halfin–Whitt regime, not only its stationary law, and it is the starting point for Corollary 2 and for the $GI/M/n$ extension in Theorems 3 and 4.
--
--   **Formalization Note** The queue is the published `ErlangA.Diffusion.IsErlangASystem` with patience rate $0$ (its abandonment clock then never moves). The diffusion is a solution of the published equation $dY=m(Y)\,dt+\sqrt{2\mu}\,dB$ with initial law $\nu$ independent of $B$. $Y_n\Rightarrow Y$ in $D[0,\infty)$ is the published `CouplingConverges`: copies with the same laws converge almost surely uniformly on compacts; since the limit has continuous paths this is equivalent to $J_1$ weak convergence. $Y_n(0)\Rightarrow\nu$ is convergence of $E\,g(Y_n(0))$ for every bounded continuous $g$.
--
--   Differences from the source:
--
--   - encoding: Y_n ⇒ Y in D[0,∞) with the J₁ topology → CouplingConverges (Skorokhod coupling, a.s. uniform convergence on compacts); reason: equivalent because the limit diffusion has continuous paths
--   - encoding: the sequence of M/M/n queues, each on its own space → all queues on one probability space; reason: weak convergence depends only on the laws, and any family of laws is realized on a product space
--   - encoding: the M/M/n queue → IsErlangASystem with abandonment rate 0, carrying an unused independent Poisson clock R; reason: with rate 0 the term R(0·…) = 0 vanishes, and the extra independent primitive does not change the law of Q
--   - reading: Y is a diffusion process with m(x), σ²(x) → Y solves Y(t) = Y(0) + ∫₀ᵗ m(Y(u)) du + √(2μ) B(t) with Y(0) ∼ ν independent of the Brownian motion B; reason: the generator (2.16) (σ²/2)f″ + m f′ is that of this equation; σ² = 2μ gives the coefficient √(2μ)
--   - reading: the Section 2 setup (λ_n → ∞, ρ_n < 1, (2.2) with β > 0) → 0 < λ_n < nμ and (2.2) with β > 0; λ_n → ∞ is not stated; reason: it follows from (2.2), which forces λ_n/(nμ) → 1
-- source:
--   Halfin and Whitt, Heavy-Traffic Limits for Queues with Many Exponential Servers, Operations Research 29 (1981), p. 577, Theorem 2 (with (2.15), (2.16))

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace HalfinWhitt81.Stationary.Supplement

open BellWilliams2001.ThresholdPolicy ErlangA.Diffusion

/-- Halfin–Whitt (1981), Theorem 2, p. 577. For `n ≥ 1` let `Q_n` be the number-in-system process
of an `M/M/n` queue with arrival rate `λ_n`, `0 < λ_n < nμ`, and service rate `μ > 0` (the
published `IsErlangASystem` with patience rate `0`), all systems on one probability space, and
`(1 − λ_n/(nμ))√n → β > 0`. If `Y_n(0) = (Q_n(0) − n)/√n` converges in distribution to `ν`, then
there is a diffusion `Y` with drift `−μβ` on `x ≥ 0`, `−μ(x + β)` on `x ≤ 0` and infinitesimal
variance `2μ`, started from `ν` independently of its Brownian motion, such that `Y_n ⇒ Y` in
`D[0, ∞)` (coupling form `CouplingConverges`). -/
theorem theorem_2 (μ β : ℝ) (hμ : 0 < μ) (hβ : 0 < β) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n ∧ lam n < n * μ)
    (hβlim : Tendsto (fun n : ℕ => (1 - lam n / (n * μ)) * Real.sqrt n) atTop (𝓝 β))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S R : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsErlangASystem P n (lam n) μ 0 (A n) (S n) (R n) (Q n))
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (scaled n (Q n) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (b : ℝ≥0 → Ω' → ℝ)
        (q : Ω' → ℝ → ℝ),
        IsDiffusionSolution P' μ β 0 (ν : Measure ℝ) b q ∧
        CouplingConverges P P' (fun n => scaled n (Q n)) (fun ω t (_ : Fin 1) => q ω t) := by sorry

end HalfinWhitt81.Stationary.Supplement
