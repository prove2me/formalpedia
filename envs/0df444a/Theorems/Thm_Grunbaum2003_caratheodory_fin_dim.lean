-- Prove2me | Theorems.Thm_Grunbaum2003_caratheodory_fin_dim
-- name    : Grunbaum2003.caratheodory_fin_dim
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T06:46:32.653371+00:00
-- url     : https://prove2.me/theorems/0d255d92-11df-4aca-9a01-1888908f3f19
-- title:
--   Carathéodory's theorem in finite dimensions
-- statement:
--   For every natural dimension d, every set S in real d-dimensional space, and every point x of the convex hull of S, there is a finite subset T of S with at most d+1 elements such that x lies in the convex hull of T.
-- source:
--   Branko Grünbaum, Convex Polytopes, second edition (2003), Â§2.5, Theorem 6 (2.5.6), printed p.25 / source.pdf p.43; characteristic cone and line-free sets: printed p.24 / PDF42; extreme points: Â§2.4, printed p.17 / PDF35.

import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions

set_option autoImplicit false
open scoped Pointwise

namespace Grunbaum2003

theorem caratheodory_fin_dim {d : ℕ}
    (S : Set (Fin d → ℝ)) (x : Fin d → ℝ) (hx : x ∈ convexHull ℝ S) :
    ∃ T : Finset (Fin d → ℝ), T.card ≤ d + 1 ∧ ↑T ⊆ S ∧ x ∈ convexHull ℝ ↑T := by sorry

end Grunbaum2003
