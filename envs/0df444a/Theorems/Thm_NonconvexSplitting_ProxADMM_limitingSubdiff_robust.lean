-- Prove2me | Theorems.Thm_NonconvexSplitting_ProxADMM_limitingSubdiff_robust
-- name    : NonconvexSplitting.ProxADMM.limitingSubdiff_robust
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T13:14:20.297681+00:00
-- url     : https://prove2.me/theorems/c7e2643b-36bf-408a-9c99-79a08643f35f
-- title:
--   Robustness of the limiting subdifferential (Eq. (3))
-- statement:
--   Let $f : \mathbb{R}^m \to (-\infty, +\infty]$ be proper, and let $u \in \mathbb{R}^m$ with $f(u) < +\infty$. Suppose $u^t \to u$ with $f(u^t) \to f(u)$, $v^t \to v$, and $v^t \in \partial f(u^t)$ for every $t$, where $\partial$ is the limiting subdifferential. Then
--   $$
--   v \in \partial f(u).
--   $$
--   Equivalently, $\{v : \exists\, u^t \xrightarrow{f} u,\ v^t \to v,\ v^t \in \partial f(u^t)\} \subseteq \partial f(u)$: the graph of $\partial f$ is closed along $f$-attentive sequences.
--
--   This is the property used to pass to the limit in the optimality conditions of the ADMM subproblems.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 3, Eq. (3)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
open NonconvexSplitting.Shared

open Filter Topology
open scoped InnerProductSpace

namespace NonconvexSplitting.ProxADMM

/-- Eq. (3) of Li–Pong (p. 3): robustness of the limiting subdifferential. -/
theorem limitingSubdiff_robust {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → EReal)
    (hf : IsProperFn f) (u v : EuclideanSpace ℝ (Fin m)) (hu : f u ≠ ⊤)
    (us vs : ℕ → EuclideanSpace ℝ (Fin m))
    (hus : Tendsto us atTop (𝓝 u)) (hfus : Tendsto (fun t => f (us t)) atTop (𝓝 (f u)))
    (hvs : Tendsto vs atTop (𝓝 v)) (hmem : ∀ t, vs t ∈ LimitingSubdiff f (us t)) :
    v ∈ LimitingSubdiff f u := by sorry

end NonconvexSplitting.ProxADMM
