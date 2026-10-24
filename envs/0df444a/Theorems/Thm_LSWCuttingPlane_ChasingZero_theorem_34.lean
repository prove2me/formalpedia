-- Prove2me | Theorems.Thm_LSWCuttingPlane_ChasingZero_theorem_34
-- name    : LSWCuttingPlane.ChasingZero.theorem_34
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:35.870291+00:00
-- url     : https://prove2.me/theorems/90d4d7f6-f661-49c3-803b-fbbe081f670c
-- title:
--   Theorem 34, p. 43 — under i^(k) = argmaxᵢ |yᵢ^(k)|, w.p. ≥ 1 − p, ‖x⃗^(k)‖∞ ≤ 2(c+R) log(4mk²/p) for all k
-- statement:
--   **The stochastic chasing $\vec 0$ game.** Fix constants $c>0$ and $R>0$ and a dimension $m\ge1$. A point starts at $\vec x^{(1)}=\vec 0\in\mathbb R^m$. In every round $k=1,2,\dots$:
--   1. the stochastic adversary picks a distribution $\mathcal D^{(k)}$ on $\mathbb R^m$ with $\mathbb E_{\mathcal D^{(k)}}\vec\Delta=\vec 0$ and $\|\vec\Delta\|_2\le c$ for all $\vec\Delta$ in its support;
--   2. the adversary picks an observation $\vec y^{(k)}\in\mathbb R^m$ with $\|\vec y^{(k)}-\vec x^{(k)}\|_\infty\le R$;
--   3. the player picks a coordinate $i^{(k)}$ using only $\vec y^{(k)}$;
--   4. a step $\vec\Delta^{(k)}$ is sampled from $\mathcal D^{(k)}$, and $x^{(k+1)}_{i^{(k)}}=0$, $x^{(k+1)}_j=x^{(k)}_j+\Delta^{(k)}_j$ for $j\ne i^{(k)}$.
--
--   The adversary may choose $\mathcal D^{(k)}$ and $\vec y^{(k)}$ adaptively, using everything that has happened before round $k$'s step is sampled.
--
--   **Theorem 34.** If the player uses the strategy $i^{(k)}=\operatorname{argmax}_i|y^{(k)}_i|$, then for every $p\in(0,1]$, with probability at least $1-p$,
--   $$\|\vec x^{(k)}\|_\infty\le2(c+R)\log\big(4mk^2/p\big)\qquad\text{for all }k\ge1.$$
--
--   In the paper this game abstracts the maintenance of approximate leverage scores inside the new cutting plane method: the player is the algorithm, which can afford to recompute one coordinate exactly per step, and the theorem says that the accumulated error stays logarithmic in the number of rounds.
--
--   **Formalization Note** The randomness is a probability space $(\Omega,\mu)$ with a filtration $(\mathcal F_k)_{k\ge0}$, where $\mathcal F_k$ is what is known before the step of the paper's round $k+1$ is sampled. Lean's round $k$ is the paper's round $k+1$: `Δ k`, `y k`, `traj Δ y k` are $\vec\Delta^{(k+1)}$, $\vec y^{(k+1)}$, $\vec x^{(k+1)}$, so the bound reads $\log(4m(k+1)^2/p)$. The rules of the game are the hypotheses: $\vec\Delta^{(k+1)}$ is $\mathcal F_{k+1}$-measurable, $\vec y^{(k+1)}$ is $\mathcal F_k$-measurable (chosen before the step is drawn), every coordinate of $\vec\Delta^{(k+1)}$ has conditional mean $0$ given $\mathcal F_k$, $\sum_i(\Delta_i)^2\le c^2$ everywhere, and $\|\vec y-\vec x\|_\infty\le R$ on the actual trajectory. Taking $\mathcal D^{(k)}$ to be the conditional law of the step given the past is the standard reading of an adaptive adversary; every adversary of the paper yields such a process. The paper's prose writes $\|\vec\Delta\|_2^2\le c$ while Algorithm 4 and the proof use $\|\vec\Delta\|_2\le c$; the latter is formalized. The player's strategy is a function of $\vec y^{(k)}$ alone by construction, with ties broken by least index. Logarithms are natural; $0<p\le1$ is the paper's "probability at least $1-p$".
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, pp. 42–43, §7.2, Algorithm 4 and Theorem 34

import Mathlib
import Definitions.Def_LSWCuttingPlane_ChasingZero_Setting

open MeasureTheory

namespace LSWCuttingPlane.ChasingZero

/-- Theorem 34 (p. 43). Round `k : ℕ` of the Lean model is the paper's round `k + 1`:
`Δ k`, `y k` are `Δ⃗^(k+1)`, `y⃗^(k+1)`, and `traj Δ y k` is `x⃗^(k+1)`, so the paper's
bound `2(c + R) log(4 m k² / p)` for `x⃗^(k)` reads with `k + 1` in place of `k`.
`ℱ k` is the information available before `Δ⃗^(k+1)` is sampled. -/
theorem theorem_34 {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) {m : ℕ} [NeZero m] (c R p : ℝ) (hc : 0 < c) (hR : 0 < R)
    (hp : 0 < p) (hp1 : p ≤ 1) (Δ y : ℕ → Ω → Fin m → ℝ)
    (hΔ_adapted : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Δ k))
    (hy_adapted : ∀ k, StronglyMeasurable[ℱ k] (y k))
    (hΔ_mean : ∀ k i, μ[fun ω => Δ k ω i | ℱ k] =ᵐ[μ] 0)
    (hΔ_norm : ∀ k ω, ∑ i, (Δ k ω i) ^ 2 ≤ c ^ 2)
    (hy_close : ∀ k ω, ‖y k ω - traj Δ y k ω‖ ≤ R) :
    ENNReal.ofReal (1 - p) ≤
      μ {ω | ∀ k : ℕ, ‖traj Δ y k ω‖ ≤
        2 * (c + R) * Real.log (4 * (m : ℝ) * ((k : ℝ) + 1) ^ 2 / p)} := by sorry

end LSWCuttingPlane.ChasingZero
