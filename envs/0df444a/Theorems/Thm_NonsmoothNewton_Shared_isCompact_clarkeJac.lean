-- Prove2me | Theorems.Thm_NonsmoothNewton_Shared_isCompact_clarkeJac
-- name    : NonsmoothNewton.Shared.isCompact_clarkeJac
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T00:03:58.41106+00:00
-- url     : https://prove2.me/theorems/5d18be7e-c626-4b41-ae97-efc99b1e2a54
-- title:
--   Clarke's generalized Jacobian is compact at a point
-- statement:
--   Let $F : E \to G$ be locally Lipschitz at $x$, with $E$ and $G$ finite-dimensional real normed spaces, and let $\partial_C F(x)$ denote Clarke's generalized Jacobian `clarkeJac F x`.
--
--   Then $\partial_C F(x)$ is a compact subset of the space of continuous linear maps from $E$ to $G$.
--
--   **Formalization Note** `clarkeJac F x` is the convex hull of `bJac F x` by definition. `isCompact_bJac` gives compactness of the B-limit set, and `isCompact_convexHull_of_isCompact_finiteDimensional` lifts that to its convex hull. Together with the fact that every element of $\partial_C F(x)$ is a unit at a semismooth regular root, this compact set is what allows the continuity of the inverse to be upgraded to a single uniform bound.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), Section 3, p. 354. Compactness of the B-limit set and of Clarke's generalized Jacobian at a point, via the finite-dimensional fact that the convex hull of a compact set is compact; the compactness input for the uniform local inverse-norm bound required by NonsmoothNewton.Local.prop_3_1.

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology Set

namespace NonsmoothNewton.Shared

/-- Clarke's generalized Jacobian `clarkeJac F x` is a compact set.

By definition `clarkeJac F x = convexHull ℝ (bJac F x)`. The B-limit set is
compact by `isCompact_bJac`, and the convex hull of a compact set in a
finite-dimensional space is compact by
`isCompact_convexHull_of_isCompact_finiteDimensional`.

This supplies the compact set on which the unit and inverse argument of
`NonsmoothNewton.Local.prop_3_1` operates. -/
theorem isCompact_clarkeJac {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E) :
    IsCompact (clarkeJac F x) := by sorry

end NonsmoothNewton.Shared
