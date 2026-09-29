-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_g_theorem
-- name    : Grunbaum2003.simplicial_g_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:21:57.4508+00:00
-- url     : https://prove2.me/theorems/9903648b-8c98-4b16-8050-7a991c747e01
-- title:
--   g-theorem — Complete characterization of simplicial face vectors
-- statement:
--   An extended integer vector f = (1,f₀,…,f_{d−1}) is the face vector of a simplicial d-polytope if and only if it equals g times Björner’s matrix M_d for an M-sequence g indexed through floor(d/2).
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §10.6, g-theorem in Björner matrix formulation (unnumbered 2003 additional notes), printed pp. 198a–198b / PDF pp. 235–236; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

/-- Full g-theorem, Grünbaum (2003), §10.6, pp.198a–198b/PDF235–236.
An extended integer f-vector (1,f₀,...,f_{d-1}) is realizable by a simplicial
d-polytope iff it is g M_d for an M-sequence g of length floor(d/2)+1.
`f j.succ` counts j-dimensional faces; `f 0` is the empty-face coordinate.
The unconstrained tail of g is unused on both sides of its finite condition.
The polytope and face-count predicates are the existing book-local adapters. -/
theorem simplicial_g_theorem (d : ℕ) (f : Fin (d + 1) → ℤ) :
    (f 0 = 1 ∧ ∃ P : Set (Fin d → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ k : Fin (d + 1),
        f k = ∑ j ∈ Finset.range (d / 2 + 1),
          (g j : ℤ) * gTheoremMatrix d j k.val := by sorry

end Grunbaum2003
