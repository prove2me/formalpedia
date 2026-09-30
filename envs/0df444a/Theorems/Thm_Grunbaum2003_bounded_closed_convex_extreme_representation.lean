-- Prove2me | Theorems.Thm_Grunbaum2003_bounded_closed_convex_extreme_representation
-- name    : Grunbaum2003.bounded_closed_convex_extreme_representation
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-30T08:38:32.004123+00:00
-- url     : https://prove2.me/theorems/37421203-d462-49d1-ba51-f669e79b3029
-- title:
--   Bounded closed convex sets are the convex hull of their extreme points
-- statement:
--   For every natural dimension d, every nonempty bounded closed convex set K in real d-dimensional space equals the convex hull of its extreme points. This is the bounded case of Theorem 2.5.6, via Krein–Milman plus the compactness of the convex hull.
-- source:
--   Branko Grünbaum, Convex Polytopes, second edition (2003), Â§2.5, Theorem 6 (2.5.6), printed p.25 / source.pdf p.43; characteristic cone and line-free sets: printed p.24 / PDF42; extreme points: Â§2.4, printed p.17 / PDF35.

import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
open scoped Pointwise

namespace Grunbaum2003

theorem bounded_closed_convex_extreme_representation {d : ℕ}
    (K : Set (Fin d → ℝ)) (hne : K.Nonempty) (hb : Bornology.IsBounded K)
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) :
    K = convexHull ℝ (K.extremePoints ℝ) := by sorry

end Grunbaum2003
