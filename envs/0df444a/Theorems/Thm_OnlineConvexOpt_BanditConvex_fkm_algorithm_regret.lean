-- Prove2me | Theorems.Thm_OnlineConvexOpt_BanditConvex_fkm_algorithm_regret
-- name    : OnlineConvexOpt.BanditConvex.fkm_algorithm_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T20:40:38.812459+00:00
-- url     : https://prove2.me/theorems/e8c8c9fb-284c-4cc9-a86f-786186c289a4
-- title:
--   Theorem 6.9 — FKM algorithm regret bound (goal)
-- statement:
--   **Statement (Theorem 6.9, p. 113, PDF p. 135).** Algorithm 23 (the FKM algorithm) with
--   parameters $\eta = D/(nT^{3/4})$, $\delta = 1/T^{1/4}$ guarantees the expected regret bound
--   $$\sum_{t=1}^T \mathbb E[f_t(y_t)] - \min_{x \in K}\sum_{t=1}^T f_t(x) \le 9nDGT^{3/4} =
--   O(T^{3/4}).$$
--
--   Algorithm 23 is the bandit-feedback instantiation of the reduction (Lemma 6.5) with the
--   sphere-sampling gradient estimator (Lemma 6.7): it plays $y_t = x_t + \delta u_t$ for a
--   fresh uniform $u_t \sim S$, observes only $f_t(y_t)$, forms $g_t = \frac{n}{\delta}
--   f_t(y_t) u_t$, and runs projected gradient descent $x_{t+1} = \Pi_{K_\delta}[x_t - \eta
--   g_t]$ onto the shrunk set $K_\delta = \{z \mid (1-\delta)^{-1} z \in K\}$ (Algorithm 23
--   projects onto $K_\delta$, not $K$, to keep room for spherical sampling near the boundary).
--   This is the historically earliest bandit convex optimization algorithm, applying online
--   gradient descent to the bandit setting.
--
--   **Formalization Note.** $K$ is assumed convex, to contain the unit ball centered at $0$,
--   and to have diameter at most $D$; the cost functions $f_t$ are $G$-Lipschitz and bounded
--   by $1$ in absolute value on $K$ — the chapter's standing simplifying assumptions for
--   Algorithm 23 (p. 112), stated as explicit hypotheses. $\min_{x\in K}$ is rendered as an
--   infimum `⨅ z ∈ K`. Integrability of $f_t(y_t)$ is required explicitly for the expectation
--   to be well-defined. The bound `9nDGT^{3/4}` is the book's own explicit constant, kept
--   exactly (not rounded, and the `O(T^{3/4})` restated as the same explicit bound, since it
--   is asymptotically worse than Chapter III's full-information $\sqrt T$ rate by design, not
--   an approximation to be improved).
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 113, Theorem 6.9 (PDF p. 135)

import Mathlib
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open MeasureTheory

namespace OnlineConvexOpt.BanditConvex

/-- Theorem 6.9 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 113, PDF p. 135). Algorithm 23 (the FKM algorithm) with parameters
`η = D / (n T^{3/4})`, `δ = 1 / T^{1/4}` guarantees the following expected regret bound:
`Σ_{t=1}^T E[f_t(y_t)] - min_{x ∈ K} Σ_{t=1}^T f_t(x) ≤ 9 n D G T^{3/4} = O(T^{3/4})`.

`K ⊆ EuclideanSpace ℝ (Fin n)` contains the unit ball centered at `0` (p. 112, PDF p. 134), is
convex with diameter `≤ D`, and carries `G`-Lipschitz cost functions `f_t` bounded by `1` in
absolute value on `K` (the chapter's standing simplifying assumptions for Algorithm 23, stated
here as explicit hypotheses). `Kδ` is the shrunk Minkowski set `{z | (1 - δ)⁻¹ z ∈ K}` (p. 112,
PDF p. 134) that Algorithm 23 projects onto, kept as its own object (never conflated with `K`).
`u_t ∼ S` is the round-`t` uniformly drawn unit vector, `y_t = x_t + δ u_t` the played point, and
`g_t = (n/δ) f_t(y_t) u_t` the gradient estimate driving the projected-gradient update
`x_{t+1} = Π_{Kδ}[x_t - η g_t]` of line 5 of Algorithm 23 (reusing `IsMetricProjection` from
Chapter III's `Protocol`). -/
theorem fkm_algorithm_regret
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (K Kδ : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K)
    (hKball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (D G : ℝ) (hDpos : 0 < D) (hGpos : 0 < G)
    (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (T : ℕ) (hT : 1 ≤ T)
    (η δ : ℝ) (hη : η = D / ((n : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ)))
    (hδ : δ = 1 / (T : ℝ) ^ (1 / 4 : ℝ))
    (hKδ : ∀ z : EuclideanSpace ℝ (Fin n), z ∈ Kδ ↔ (1 - δ)⁻¹ • z ∈ K)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (hfbdd : ∀ t, ∀ x ∈ K, |f t x| ≤ 1)
    (x y u g : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hx0 : ∀ ω, x 0 ω = 0)
    (hu : ∀ t, IsUniformOnUnitSphere Prob (u t))
    (hy : ∀ t ω, y t ω = x t ω + δ • u t ω)
    (hg : ∀ t ω, g t ω = ((n : ℝ) / δ * f t (y t ω)) • u t ω)
    (hstep : ∀ t ω,
      OnlineConvexOpt.FirstOrder.IsMetricProjection Kδ (x t ω - η • g t ω) (x (t + 1) ω))
    (hint : ∀ t, Integrable (fun ω => f t (y t ω)) Prob) :
    (∑ t ∈ Finset.range T, ∫ ω, f t (y t ω) ∂Prob) - ⨅ z ∈ K, ∑ t ∈ Finset.range T, f t z ≤
      9 * n * D * G * (T : ℝ) ^ (3 / 4 : ℝ) := by sorry

end OnlineConvexOpt.BanditConvex
