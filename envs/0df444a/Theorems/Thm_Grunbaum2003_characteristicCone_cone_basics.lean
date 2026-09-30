-- Prove2me | Theorems.Thm_Grunbaum2003_characteristicCone_cone_basics
-- name    : Grunbaum2003.characteristicCone_cone_basics
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T06:46:51.063358+00:00
-- url     : https://prove2.me/theorems/2af78121-01f4-4294-a384-7de27b003c9e
-- title:
--   Characteristic cone is a convex cone; K is stable under translation by it
-- statement:
--   For every natural dimension d and every set K in real d-dimensional space, the characteristic cone of K is a convex set containing the zero vector, and K translated by any element of the characteristic cone stays inside K.
-- source:
--   Branko Grünbaum, Convex Polytopes, second edition (2003), Â§2.5, Theorem 6 (2.5.6), printed p.25 / source.pdf p.43; characteristic cone and line-free sets: printed p.24 / PDF42; extreme points: Â§2.4, printed p.17 / PDF35.

import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions

set_option autoImplicit false
open scoped Pointwise

namespace Grunbaum2003

theorem characteristicCone_cone_basics {d : ℕ}
    (K : Set (Fin d → ℝ)) :
    Convex ℝ (characteristicCone K) ∧ (0 : Fin d → ℝ) ∈ characteristicCone K ∧
    K + characteristicCone K ⊆ K := by sorry

end Grunbaum2003
