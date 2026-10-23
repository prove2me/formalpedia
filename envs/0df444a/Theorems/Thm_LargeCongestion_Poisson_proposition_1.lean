-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_proposition_1
-- name    : LargeCongestion.Poisson.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:12.811406+00:00
-- url     : https://prove2.me/theorems/76fbac1c-600c-46ea-b5d7-341cff383ff5
-- title:
--   Proposition 1, p. 16 — under (14), expected flow-loads are bounded with limits in F(d), and flows/loads converge in total variation to independent Poisson limits
-- statement:
--   Let $\Gamma^n_B$ be a sequence of Bernoulli congestion games satisfying (14) — $|\mathcal N^n| \to \infty$, $u^n = \max_i u^n_i \to 0$ and $d^n_t \to d_t$ for every type $t$ — and let $\sigma^n$ be an arbitrary sequence of mixed strategy profiles. Let $Y^n_{t,s}$ and $X^n_e$ be the random flows and loads (8), and $(y^n, x^n)$ their expectations (9). Then:
--
--   1. $(y^n, x^n)_n$ is bounded, and every accumulation point $(y, x)$ belongs to $\mathcal F(d)$;
--   2. along a subsequence with $(y^{n}, x^{n}) \to (y, x)$, $Y^n_{t,s} \to \mathrm{Poisson}(y_{t,s})$ and $X^n_e \to \mathrm{Poisson}(x_e)$ in total variation;
--   3. the limit variables $(Y_{t,s})_{t \in \mathcal T, s \in \mathcal S_t}$ are independent: the joint law of the flow vector converges in total variation to
--   $$\bigotimes_{t \in \mathcal T,\, s \in \mathcal S_t}\mathrm{Poisson}(y_{t,s}).$$
--
--   The proposition describes the large-game limit for any behavior of the players; Theorem 2 adds that equilibrium behavior produces Wardrop limits.
--
--   **Formalization Note** An accumulation point is a limit along a strictly increasing $\varphi : \mathbb N \to \mathbb N$. Convergence is assumed for every pair $(t,s)$; for $s \notin \mathcal S_t$ the expected flows are $0$, so this is the paper's convergence on $\{(t,s) : s \in \mathcal S_t\}$. Independence of the limit (c) is formalized as total-variation convergence of the joint law of $(Y^n_{t,s})_{t,s}$ on $\mathbb N^{\{(t,s)\}}$ to the product of the Poisson laws; on this countable space this is equivalent to the convergence in distribution that the paper's moment generating function argument yields. Nonempty $\mathcal S_t$ is the standing assumption of §2.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, p. 16, Proposition 1(a)–(c)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus
import Definitions.Def_LargeCongestion_Poisson_Game

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- Proposition 1, p. 16: for Bernoulli congestion games `Γ^n_B` satisfying (14) and arbitrary
mixed profiles `σ^n`, (a) the expected flow-load pairs `(y^n, x^n)` are bounded and every
accumulation point `(y, x)` (limit along a subsequence `φ`) lies in `F(d)`; (b) along that
subsequence `Y^n_{t,s} → Poisson(y_{t,s})` and `X^n_e → Poisson(x_e)` in total variation; (c) the
limits `(Y_{t,s})` are independent: the joint law of the flow vector converges in total variation
to the product of the Poisson laws. -/
theorem proposition_1 {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]
    (S : T → Finset (Finset E)) (hS : StrategiesNonempty S) (d : T → ℝ)
    (N : ℕ → ℕ) (τ : ∀ n, Fin (N n) → T) (u : ∀ n, Fin (N n) → ℝ)
    (hu : ∀ n, IsBernoulliGame (u n)) (h14 : Condition14 N τ u d)
    (σ : ∀ n, Fin (N n) → Finset E → ℝ) (hσ : ∀ n, IsMixedProfile S (τ n) (σ n)) :
    (∃ B : ℝ, ∀ n t s e,
        |expFlow (τ n) (u n) (σ n) t s| ≤ B ∧ |expLoad S (τ n) (u n) (σ n) e| ≤ B) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ (y : T → Finset E → ℝ) (x : E → ℝ),
        (∀ t s, Tendsto (fun k => expFlow (τ (φ k)) (u (φ k)) (σ (φ k)) t s) atTop
          (𝓝 (y t s))) →
        (∀ e, Tendsto (fun k => expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e) atTop
          (𝓝 (x e))) →
        IsFeasible S d y x ∧
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
