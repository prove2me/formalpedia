-- Prove2me | Theorems.Thm_Grunbaum2003_isCompact_convexHull_of_compact
-- name    : Grunbaum2003.isCompact_convexHull_of_compact
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T06:46:35.758402+00:00
-- url     : https://prove2.me/theorems/820cacac-8c97-450f-ad87-c70e09303ee3
-- title:
--   Convex hull of a compact set is compact in finite dimensions
-- statement:
--   For every natural dimension d, the convex hull of a compact set in real d-dimensional space is compact.
-- source:
--   Branko Grünbaum, Convex Polytopes, second edition (2003), Â§2.5, Theorem 6 (2.5.6), printed p.25 / source.pdf p.43; characteristic cone and line-free sets: printed p.24 / PDF42; extreme points: Â§2.4, printed p.17 / PDF35.

import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions

set_option autoImplicit false
open scoped Pointwise

namespace Grunbaum2003

theorem isCompact_convexHull_of_compact {d : ℕ}
    (s : Set (Fin d → ℝ)) (h : IsCompact s) :
    IsCompact (convexHull ℝ s) := by sorry

end Grunbaum2003
