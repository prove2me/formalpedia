-- Prove2me | Theorems.Thm_Grunbaum2003_perles_prescribed_section
-- name    : Grunbaum2003.perles_prescribed_section
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:38:55.137541+00:00
-- url     : https://prove2.me/theorems/b621f7ca-9bb5-4269-bced-08d5358b9962
-- title:
--   Theorem 5.1.10 — Simplex section through a prescribed interior point
-- statement:
--   For every full-dimensional d-polytope P with at most k+1 facets, every k-simplex T in real k-space, and every point p in the interior of T, there is a d-dimensional affine flat L containing p such that the complete section T ∩ L is affinely equivalent to P.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §5.1, Theorem 5.1.10, printed p. 74 / PDF p. 100; section convention printed p. 71 / PDF p. 97; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

set_option autoImplicit false

namespace Grunbaum2003

/-- Perles's prescribed-point section theorem, Grünbaum (2003), §5.1,
Theorem 10 (5.1.10), printed p.74 / PDF p.100.
Write the source's facet allowance as `f = k + 1`. The arbitrary k-simplex
is the convex hull of `k + 1` affinely independent points. An injective
real affine map onto the flat, mapping P exactly onto its intersection
with the simplex, expresses affine equivalence. The prescribed point is
arbitrary in the simplex interior. The zero-dimensional case has no
nonempty proper facets; its facet allowance is automatic. No positive-
dimensional restriction is added. Statement-only local staging. -/
theorem perles_prescribed_section (d k : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hfacets : (if d = 0 then 0 else faceCount P (d - 1)) ≤ k + 1)
    (v : Fin (k + 1) → (Fin k → ℝ)) (hv : AffineIndependent ℝ v)
    (p : Fin k → ℝ) (hp : p ∈ interior (convexHull ℝ (Set.range v))) :
    ∃ L : AffineSubspace ℝ (Fin k → ℝ),
      p ∈ L ∧ Module.finrank ℝ L.direction = d ∧
      ∃ A : (Fin d → ℝ) →ᵃ[ℝ] (Fin k → ℝ),
        Function.Injective A ∧ Set.range A = (L : Set (Fin k → ℝ)) ∧
          A '' P = convexHull ℝ (Set.range v) ∩ (L : Set (Fin k → ℝ)) := by sorry

end Grunbaum2003
