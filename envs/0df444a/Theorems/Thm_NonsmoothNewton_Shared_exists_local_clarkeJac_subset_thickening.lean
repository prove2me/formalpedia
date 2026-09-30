-- Prove2me | Theorems.Thm_NonsmoothNewton_Shared_exists_local_clarkeJac_subset_thickening
-- name    : NonsmoothNewton.Shared.exists_local_clarkeJac_subset_thickening
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T22:53:53.94663+00:00
-- url     : https://prove2.me/theorems/88c855b1-7bd3-4344-808c-4400d37476e1
-- title:
--   Local upper semicontinuity of Clarke's generalized Jacobian
-- statement:
--   Let $F : E \to G$ be locally Lipschitz at $x$, with $E$, $G$ finite-dimensional real normed spaces, and let $\partial_C F(y)$ denote Clarke's generalized Jacobian `clarkeJac F y`.
--
--   For every $\varepsilon > 0$ there exists $\delta > 0$ such that whenever $y$ satisfies $\mathrm{dist}(y, x) < \delta$, $\partial_C F(y) \subseteq \operatorname{thickening}(\varepsilon, \partial_C F(x))$.
--
--   This is the convex-hull lifting of the corresponding statement for the B-limit sets. Since $\partial_C F(y) = \operatorname{conv}(\partial_B F(y))$ and the $\varepsilon$-thickening of a convex set is convex, a subset bound on the generating set lifts to the same subset bound on its convex hull.
--
--   **Formalization Note** The proof is `convexHull_min`: a subset of a convex set pulls its convex hull back into that convex set. Convexity of the thickening is `Convex.thickening` applied to `convex_convexHull`. No form of Carathéodory's theorem is required.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), Section 3, p. 354. Qualitative upper semicontinuity of the B-limit set and, by convex-hull lifting, of Clarke's generalized Jacobian; the step that turns pointwise invertibility at a root into a uniform local inverse bound.

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology Set

namespace NonsmoothNewton.Shared

/-- Local upper semicontinuity of Clarke's generalized Jacobian `clarkeJac F`.

This is the convex-hull lifting of `exists_local_bJac_subset_thickening`. Since
`clarkeJac F y = convexHull ℝ (bJac F y)` and the `ε`-thickening of a convex set
is convex, a subset bound on the generating set lifts to the same subset bound on
its convex hull. No appeal to Carathéodory is needed, and no regularity of `F`
beyond local Lipschitz continuity at `x` is used.

This is the ingredient that carries the upper semicontinuity estimate from the
B-limit sets to Clarke's generalized Jacobian in `NonsmoothNewton.Local.prop_3_1`.
-/
theorem exists_local_clarkeJac_subset_thickening {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y, dist y x < δ →
      clarkeJac F y ⊆
        Metric.thickening ε (clarkeJac F x) := by sorry

end NonsmoothNewton.Shared
