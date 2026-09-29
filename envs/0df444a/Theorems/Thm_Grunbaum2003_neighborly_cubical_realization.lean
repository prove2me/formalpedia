-- Prove2me | Theorems.Thm_Grunbaum2003_neighborly_cubical_realization
-- name    : Grunbaum2003.neighborly_cubical_realization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:38:34.32499+00:00
-- url     : https://prove2.me/theorems/f3781e89-918c-4812-af02-627fc12b7392
-- title:
--   Joswig–Ziegler neighborly cubical realization
-- statement:
--   For every n > d ≥ 2 there exists a cubical d-polytope whose (floor(d/2) − 1)-skeleton is combinatorially equivalent to that of an n-cube.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §4.9, unnumbered Joswig–Ziegler existence theorem, printed p. 69b / PDF p. 95; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsCubicalDPolytope
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_standardCube

set_option autoImplicit false

namespace Grunbaum2003

/-- Joswig–Ziegler neighborly cubical realization, Grünbaum (2003),
§4.9, printed p.69b / PDF p.95. For every n > d ≥ 2, a cubical
d-polytope has the full (floor(d/2)−1)-skeleton of the n-cube.
The existing face-poset order isomorphism expresses combinatorial
skeleton equivalence across the two ambient dimensions. Since d ≥ 2,
natural subtraction in d / 2 - 1 agrees with the source's integer index.
Statement only; no coordinates or construction lemmas are asserted. -/
theorem neighborly_cubical_realization (n d : ℕ) (hd : 2 ≤ d) (hnd : d < n) :
    ∃ P : Set (Fin d → ℝ), IsCubicalDPolytope P ∧
      Nonempty (SkeletonFace P (d / 2 - 1) ≃o
        SkeletonFace (standardCube n) (d / 2 - 1)) := by sorry

end Grunbaum2003
