-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Convex_eq5_subdiff_eq_convex
-- name    : NonsmoothLojasiewicz.Convex.eq5_subdiff_eq_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:50:39.086219+00:00
-- url     : https://prove2.me/theorems/cf93d61b-0a8a-4a50-a2dc-ebaa90435b7b
-- title:
--   Eq. (5): for lsc convex $f$, limiting, Fréchet and convex subdifferentials coincide
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be lower semicontinuous, convex and somewhere finite. Then at every $x\in\mathbb R^n$ the limiting subdifferential and the Fréchet subdifferential coincide with the subdifferential of convex analysis:
--   $$\partial f(x)=\hat\partial f(x)=\{x^*\in\mathbb R^n:\ f(\cdot)-\langle x^*,\cdot\rangle\text{ has a global minimum at }x\}.$$
--
--   This identification lets every statement about the limiting subdifferential of a convex function be read with the classical subgradient inequality $f(u)\ge f(x)+\langle x^*,u-x\rangle$.
--
--   **Formalization Note** $\partial f$ and $\hat\partial f$ are the published `LimitingSubdiff` and `IsRegularSubgrad`; "lower semicontinuous, convex, somewhere finite, never $-\infty$" is the published `GammaZero`. The right-hand set is the published `subgrad f x`, which requires $f(x)$ finite and $f(x)+\langle u-x,x^*\rangle\le f(u)$ for all $u$; since $f$ is somewhere finite, $f-\langle x^*,\cdot\rangle$ cannot attain a global minimum at a point where $f=+\infty$, so this is exactly the printed set.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1211, equation (5)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

namespace NonsmoothLojasiewicz.Convex

/-- Eq. (5) of Bolte–Daniilidis–Lewis (p. 1211): for a lower semicontinuous convex function
`f : ℝⁿ → ℝ ∪ {+∞}` that is somewhere finite, the limiting subdifferential, the Fréchet
subdifferential and the subdifferential of convex analysis coincide at every point:
`∂f(x) = ∂̂f(x) = {x* : f(·) − ⟨x*, ·⟩ has a global minimum at x}`. -/
theorem eq5_subdiff_eq_convex {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (x : EuclideanSpace ℝ (Fin n)) :
    LimitingSubdiff f x = {v | IsRegularSubgrad f x v} ∧
      {v | IsRegularSubgrad f x v} = subgrad f x := by sorry

end NonsmoothLojasiewicz.Convex
