-- Prove2me | Theorems.Thm_OnlineConvexOpt_BanditConvex_spherical_gradient_estimator_identity_v2
-- name    : OnlineConvexOpt.BanditConvex.spherical_gradient_estimator_identity_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:46.480894+00:00
-- url     : https://prove2.me/theorems/a9934a12-90d8-4fb5-a30c-d1e23a82d152
-- title:
--   Lemma 6.7 — Sphere-sampling gradient estimator identity $\mathbb E[f(x+\delta u)u]=\frac{\delta}{n}\nabla\hat f_\delta(x)$ (continuous $f$)
-- statement:
--   **Statement (Lemma 6.7).** Fix $\delta>0$ and $n\ge1$. Let $f:\mathbb R^n\to\mathbb R$ be continuous, let $\hat f_\delta(x)=\mathbb E_{v\in B}[f(x+\delta v)]$ be its $\delta$-smoothed version (6.4), and let $u\sim S$ be a uniformly drawn unit vector. Then
--   $$\mathbb E_{u\in S}\bigl[f(x+\delta u)\,u\bigr]=\frac\delta n\,\nabla\hat f_\delta(x).$$
--
--   **Formalization Note.** The retired statement imposed no regularity on $f$; since the right-hand side depends on $f$ only up to Lebesgue-null sets while the left-hand side sees $f$ on the null sphere $x+\delta S$, it was refuted by the indicator of a point. The chapter's cost functions are convex, hence continuous (and Corollary 6.8 states "a continuous function $f$" explicitly); `hfcont : Continuous f` is the hypothesis the proof's Stokes-theorem step needs, and `hn : 0 < n` records the dimension. `IsUniformOnUnitSphere` is now the `_v2` version, which additionally requires the random vector to be measurable (otherwise `Measure.map` is the zero measure and the rotation-invariance clause is vacuous). The gradient of $\hat f_\delta$ at $x$ is recorded via `HasGradientAt` and integrability of $f(x+\delta u)u$ remains an explicit hypothesis, as before.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 110, Lemma 6.7 (PDF p. 132)

import Mathlib
import Definitions.Def_OnlineConvexOpt_BanditConvex_SmoothedFunction
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere_v2

open MeasureTheory

namespace OnlineConvexOpt.BanditConvex

/-- Lemma 6.7 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3,
p. 110, PDF p. 132). Fix `δ > 0`. Let `f : ℝⁿ → ℝ` (`n ≥ 1`) be continuous, let `f̂_δ` be as
defined in (6.4) (`SmoothedFunction`), and let `u` be a uniformly drawn unit vector `u ∼ S`.
Then `E_{u ∈ S}[f(x + δu) u] = (δ/n) ∇f̂_δ(x)`.

Corrected version: the retired statement put no regularity on `f`, but the right-hand side
depends on `f` only up to Lebesgue-null sets while the left-hand side sees `f`'s values on the
null sphere `x + δS`, so the identity fails for discontinuous `f`; continuity (the chapter's
cost functions are convex, hence continuous — Corollary 6.8 states "a continuous function `f`"
explicitly) is what the proof's Stokes-theorem step needs. `IsUniformOnUnitSphere` is the
`_v2` version, which requires `U` to be measurable (so that its law is genuinely pinned
down). -/
theorem spherical_gradient_estimator_identity_v2
    {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfcont : Continuous f)
    (δ : ℝ) (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n))
    (U : Ω → EuclideanSpace ℝ (Fin n)) (hU : IsUniformOnUnitSphere Prob U)
    (grad : EuclideanSpace ℝ (Fin n)) (hgrad : HasGradientAt (SmoothedFunction f δ) grad x)
    (hint : Integrable (fun ω => f (x + δ • U ω) • U ω) Prob) :
    (∫ ω, f (x + δ • U ω) • U ω ∂Prob) = (δ / n) • grad := by sorry

end OnlineConvexOpt.BanditConvex
