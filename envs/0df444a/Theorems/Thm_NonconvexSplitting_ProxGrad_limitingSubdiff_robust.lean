-- Prove2me | Theorems.Thm_NonconvexSplitting_ProxGrad_limitingSubdiff_robust
-- name    : NonconvexSplitting.ProxGrad.limitingSubdiff_robust
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T19:14:22.350978+00:00
-- url     : https://prove2.me/theorems/3ccb1b36-664f-4e67-a8c1-18d1d00f23e6
-- title:
--   Eq. (3): robustness of the limiting subdifferential
-- statement:
--   Let $f : \mathbb{R}^n \to (-\infty, +\infty]$ be proper and let $x \in \operatorname{dom} f$. Suppose $x^t \to x$ with $f(x^t) \to f(x)$, $v^t \to v$, and $v^t \in \partial f(x^t)$ for each $t$, where $\partial$ is the limiting subdifferential. Then $v \in \partial f(x)$:
--   $$
--   \bigl\{ v \in \mathbb{R}^n : \exists\, x^t \xrightarrow{f} x,\ v^t \to v,\ v^t \in \partial f(x^t) \bigr\} \subseteq \partial f(x).
--   $$
--
--   This closedness property is what allows stationarity to pass to the limit along a convergent subsequence of iterates.
--
--   **Formalization Note** The hypothesis $f(x) < +\infty$ records that the paper defines $\partial f(x)$ only at points of $\operatorname{dom} f$; $f(x^t) \to f(x)$ is convergence in `EReal`.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 3, Eq. (3)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
open NonconvexSplitting.Shared

open Filter Topology

namespace NonconvexSplitting.ProxGrad

/-- Eq. (3) of Li–Pong (p. 3): robustness of the limiting subdifferential. -/
theorem limitingSubdiff_robust {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : ∀ y, f y ≠ ⊥) (x v : EuclideanSpace ℝ (Fin n)) (hx : f x ≠ ⊤)
    (xs vs : ℕ → EuclideanSpace ℝ (Fin n))
    (hxs : Tendsto xs atTop (𝓝 x)) (hfxs : Tendsto (fun t => f (xs t)) atTop (𝓝 (f x)))
    (hvs : Tendsto vs atTop (𝓝 v)) (hmem : ∀ t, vs t ∈ LimitingSubdiff f (xs t)) :
    v ∈ LimitingSubdiff f x := by sorry

end NonconvexSplitting.ProxGrad
