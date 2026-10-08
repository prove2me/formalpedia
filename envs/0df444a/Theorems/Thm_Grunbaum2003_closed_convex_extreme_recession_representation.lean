-- Prove2me | Theorems.Thm_Grunbaum2003_closed_convex_extreme_recession_representation
-- name    : Grunbaum2003.closed_convex_extreme_recession_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T19:02:26.447693+00:00
-- url     : https://prove2.me/theorems/2900d8cc-a420-46c3-8f3e-113579312143
-- title:
--   Theorem 2.5.6 — Extreme-point and recession representation
-- statement:
--   For every natural dimension d and every line-free, closed convex set K in real d-dimensional space, K equals the Minkowski sum of its characteristic cone and the convex hull of its extreme points. The convex hull is not topologically closed in this formula. For the empty set, the characteristic-cone convention still gives the equality of empty sets.
-- source:
--   Branko Grünbaum, Convex Polytopes, second edition (2003), §2.5, Theorem 6 (2.5.6), printed p.25 / source.pdf p.43; characteristic cone and line-free sets: printed p.24 / PDF42; extreme points: §2.4, printed p.17 / PDF35.

import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions

set_option autoImplicit false
open scoped Pointwise

namespace Grunbaum2003

theorem closed_convex_extreme_recession_representation {d : ℕ}
    (K : Set (Fin d → ℝ)) (hline : IsLineFree K)
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) :
    K = characteristicCone K + convexHull ℝ (K.extremePoints ℝ) := by sorry


end Grunbaum2003
