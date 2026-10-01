-- Prove2me | Theorems.Thm_Grunbaum2003_closed_convex_line_free_extremePoint_exists
-- name    : Grunbaum2003.closed_convex_line_free_extremePoint_exists
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T06:46:46.086747+00:00
-- url     : https://prove2.me/theorems/76a536d4-ef0e-4d90-87cb-886fe4cfafde
-- title:
--   Line-free closed convex sets have an extreme point
-- statement:
--   For every natural dimension d, every nonempty closed convex line-free set K in real d-dimensional space has an extreme point.
-- source:
--   Branko Grünbaum, Convex Polytopes, second edition (2003), Â§2.5, Theorem 6 (2.5.6), printed p.25 / source.pdf p.43; characteristic cone and line-free sets: printed p.24 / PDF42; extreme points: Â§2.4, printed p.17 / PDF35.

import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions

set_option autoImplicit false
open scoped Pointwise

namespace Grunbaum2003

theorem closed_convex_line_free_extremePoint_exists {d : ℕ}
    (K : Set (Fin d → ℝ)) (hne : K.Nonempty) (hline : IsLineFree K)
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) :
    (K.extremePoints ℝ).Nonempty := by sorry

end Grunbaum2003
