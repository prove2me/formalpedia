-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_theorem_2
-- name    : LargeCongestion.Poisson.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:25.036645+00:00
-- url     : https://prove2.me/theorems/7756a6de-842d-49fd-9631-f5a4b46c44cc
-- title:
--   Theorem 2, p. 19 — Bayesian Nash equilibria of Bernoulli congestion games converge to Poisson limits whose means are Wardrop equilibria of the game with costs c̆_e
-- statement:
--   Let $\Gamma^n_B$ be a sequence of Bernoulli congestion games on a common structure (finite resources $\mathcal E$, nonnegative weakly increasing costs $c_e$, finite types $\mathcal T$ with nonempty strategy sets $\mathcal S_t$), satisfying (14) — $|\mathcal N^n| \to \infty$, $\max_i u^n_i \to 0$, $d^n_t \to d_t$ — and (18): there are $\nu$ and $d_{\max} > \sum_t d_t$ with $\mathsf E[|\Delta^2 c_e(1+V)|] \le \nu$ for all $e$, $V \sim \mathrm{Poisson}(d_{\max})$. Let $\hat\sigma^n$ be a Bayesian Nash equilibrium of $\Gamma^n_B$ for every $n$, with expected flow-load pairs $(\hat y^n, \hat x^n)$ (9). Then:
--
--   1. $(\hat y^n, \hat x^n)_n$ is bounded;
--   2. every accumulation point $(\hat y, \hat x)$ is a Wardrop equilibrium of the nonatomic game $\breve\Gamma^\infty$ with demands $d$ and costs $\breve c_e(x) = \mathsf E[c_e(1+X)]$, $X \sim \mathrm{Poisson}(x)$: $(\hat y, \hat x) \in \mathcal F(d)$ and
--   $$\hat y_{t,s} > 0 \implies \sum_{e \in s}\breve c_e(\hat x_e) \le \sum_{e \in s'}\breve c_e(\hat x_e) \qquad \text{for all } s, s' \in \mathcal S_t ;$$
--   3. along every such convergent subsequence, $Y^n_{t,s} \to Y_{t,s} \sim \mathrm{Poisson}(\hat y_{t,s})$ and $X^n_e \to X_e \sim \mathrm{Poisson}(\hat x_e)$ in total variation, where the $Y_{t,s}$ are independent.
--
--   Equilibria of large atomic games with rare participation are thus described by a nonatomic Wardrop model for the means, with costs that average over Poisson-distributed congestion, while the flows themselves remain Poisson-random in the limit.
--
--   **Formalization Note** Accumulation points are limits along strictly increasing $\varphi$; the laws are image measures of the product probability of participations and mixed strategies, not free parameters. Independence is formalized as total-variation convergence of the joint law of the flow vector $(Y^n_{t,s})_{t, s \in \mathcal S_t}$ to the product of the $\mathrm{Poisson}(\hat y_{t,s})$ laws. In (18) the expectation is a convergent series bounded by $\nu \in \mathbb R$ (the page's $\nu \in \mathbb N$ is read as $\mathbb R$, a weaker hypothesis); without summability a fast-growing cost such as $c_e(k) = k!$ would satisfy the bound through Lean's default value $0$ of a divergent `tsum`. Nonempty $\mathcal S_t$ and the cost conventions are the standing assumptions of §2.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, p. 19, Theorem 2

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus
import Definitions.Def_LargeCongestion_Poisson_Game

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- Theorem 2, p. 19: for Bernoulli congestion games `Γ^n_B` satisfying (14) and (18) and any
sequence of Bayesian Nash equilibria `σ̂^n`, the expected flow-load pairs `(ŷ^n, x̂^n)` are bounded
and every accumulation point `(ŷ, x̂)` is a Wardrop equilibrium of `Γ̆^∞` (demands `d`, costs
`c̆_e`); along the convergent subsequence `Y^n_{t,s} → Poisson(ŷ_{t,s})` and
`X^n_e → Poisson(x̂_e)` in total variation, with the `Y_{t,s}` independent (joint total-variation
convergence of the flow vector to the product of the Poisson laws). -/
theorem theorem_2 {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]
    (S : T → Finset (Finset E)) (hS : StrategiesNonempty S) (c : E → ℕ → ℝ)
    (hc : IsCostFamily c) (d : T → ℝ) (ν dmax : ℝ) (h18 : Condition18 c d ν dmax)
    (N : ℕ → ℕ) (τ : ∀ n, Fin (N n) → T) (u : ∀ n, Fin (N n) → ℝ)
    (hu : ∀ n, IsBernoulliGame (u n)) (h14 : Condition14 N τ u d)
    (σ : ∀ n, Fin (N n) → Finset E → ℝ) (hσ : ∀ n, IsBNE S c (τ n) (u n) (σ n)) :
    (∃ B : ℝ, ∀ n t s e,
        |expFlow (τ n) (u n) (σ n) t s| ≤ B ∧ |expLoad S (τ n) (u n) (σ n) e| ≤ B) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ (y : T → Finset E → ℝ) (x : E → ℝ),
        (∀ t s, Tendsto (fun k => expFlow (τ (φ k)) (u (φ k)) (σ (φ k)) t s) atTop
          (𝓝 (y t s))) →
        (∀ e, Tendsto (fun k => expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e) atTop
          (𝓝 (x e))) →
        IsWardrop S (cBreve c) d y x ∧
          (∀ t, ∀ s ∈ S t, Tendsto (fun k => MarkovChainCLT.tvDist
              (law (u (φ k)) (σ (φ k)) (flowRV (τ (φ k)) t s))
              (poissonMeasure (y t s).toNNReal)) atTop (𝓝 0)) ∧
          (∀ e, Tendsto (fun k => MarkovChainCLT.tvDist
              (law (u (φ k)) (σ (φ k)) (loadRV e))
              (poissonMeasure (x e).toNNReal)) atTop (𝓝 0)) ∧
          Tendsto (fun k => MarkovChainCLT.tvDist
              (law (u (φ k)) (σ (φ k)) (flowVec S (τ (φ k))))
              (Measure.pi fun p : FlowIdx S => poissonMeasure (y p.1.1 p.1.2).toNNReal))
            atTop (𝓝 0) := by sorry

end LargeCongestion.Poisson
