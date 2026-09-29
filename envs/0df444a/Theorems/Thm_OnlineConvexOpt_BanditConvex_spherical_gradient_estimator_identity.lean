-- Prove2me | Theorems.Thm_OnlineConvexOpt_BanditConvex_spherical_gradient_estimator_identity
-- name    : OnlineConvexOpt.BanditConvex.spherical_gradient_estimator_identity
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:40:05.599987+00:00
-- url     : https://prove2.me/theorems/f4515280-1f58-4ea5-9beb-9c269891109b
-- title:
--   Lemma 6.7 — the spherical gradient estimator identity
-- statement:
--   **Statement (Lemma 6.7, p. 110, PDF p. 132).** Fix $\delta > 0$. Let $\hat f_\delta(x)$
--   be as defined in (6.4), and let $u$ be a uniformly drawn unit vector $u \sim S$. Then
--   $\mathbb E_{u \in S}[f(x+\delta u)\, u] = \frac{\delta}{n} \nabla \hat f_\delta(x)$.
--
--   This identity is what makes the sphere-sampling gradient estimator $g(x) = \frac{n}{\delta}
--   f(x+\delta u)u$ unbiased for $\nabla \hat f_\delta$ (the linear case then makes it unbiased
--   for $\nabla f$ itself), by an application of Stokes' theorem relating the ball integral
--   defining $\hat f_\delta$ to the sphere integral defining the estimator's expectation.
--
--   **Formalization Note.** `grad` is the gradient of `SmoothedFunction f δ` at `x`, recorded
--   via Mathlib's `HasGradientAt` (so the identity's hypothesis is that this gradient exists,
--   matching the book's implicit assumption that $\hat f_\delta$ is differentiable).
--   Integrability of $f(x+\delta u)u$ is required as an explicit hypothesis for the expectation
--   on the left to be well-defined.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 110, Lemma 6.7 (PDF p. 132)

import Mathlib
import Definitions.Def_OnlineConvexOpt_BanditConvex_SmoothedFunction
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere

open MeasureTheory

namespace OnlineConvexOpt.BanditConvex

/-- Lemma 6.7 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3,
p. 110, PDF p. 132). Fix `δ > 0`. Let `f̂_δ` be as defined in (6.4) (`SmoothedFunction`), and let
`u` be a uniformly drawn unit vector `u ∼ S`. Then `E_{u ∈ S}[f(x + δu) u] = (δ/n) ∇f̂_δ(x)`. -/
theorem spherical_gradient_estimator_identity
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (δ : ℝ) (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n))
    (U : Ω → EuclideanSpace ℝ (Fin n)) (hU : IsUniformOnUnitSphere Prob U)
    (grad : EuclideanSpace ℝ (Fin n)) (hgrad : HasGradientAt (SmoothedFunction f δ) grad x)
    (hint : Integrable (fun ω => f (x + δ • U ω) • U ω) Prob) :
    (∫ ω, f (x + δ • U ω) • U ω ∂Prob) = (δ / n) • grad := by sorry

end OnlineConvexOpt.BanditConvex
