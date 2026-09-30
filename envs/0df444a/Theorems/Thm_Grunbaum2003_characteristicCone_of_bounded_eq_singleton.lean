-- Prove2me | Theorems.Thm_Grunbaum2003_characteristicCone_of_bounded_eq_singleton
-- name    : Grunbaum2003.characteristicCone_of_bounded_eq_singleton
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T08:38:35.226309+00:00
-- url     : https://prove2.me/theorems/23c29507-0f9f-4890-bd4c-57dda5cccdae
-- title:
--   Characteristic cone of a bounded nonempty set is trivial
-- statement:
--   For every natural dimension d and every nonempty bounded set K in real d-dimensional space, the characteristic cone of K is the singleton {0}: a nonzero recession direction would produce an unbounded ray through any point of K.
-- source:
--   Branko Grünbaum, Convex Polytopes, second edition (2003), Â§2.5, Theorem 6 (2.5.6), printed p.25 / source.pdf p.43; characteristic cone and line-free sets: printed p.24 / PDF42; extreme points: Â§2.4, printed p.17 / PDF35.

import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
open scoped Pointwise

namespace Grunbaum2003

theorem characteristicCone_of_bounded_eq_singleton {d : ℕ}
    (K : Set (Fin d → ℝ)) (hne : K.Nonempty) (hb : Bornology.IsBounded K) :
    characteristicCone K = {0} := by sorry

end Grunbaum2003
