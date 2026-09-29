-- Prove2me | Theorems.Thm_Grunbaum2003_polytope_iff_polytope_projections
-- name    : Grunbaum2003.polytope_iff_polytope_projections
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:39:11.786269+00:00
-- url     : https://prove2.me/theorems/b7ad61d0-1e06-459e-90c5-3f6a4b455bf0
-- title:
--   Theorem 5.1.8 — Recognition from projections
-- statement:
--   For d at least 3, a bounded convex subset K of real d-dimensional space is a finite convex hull if and only if there is one dimension j with 2 ≤ j < d such that every surjective affine map from real d-space onto real j-space sends K to a finite convex hull. The dimension j is chosen before the maps; the finite witness may depend on the map. Empty and lower-dimensional sets remain included.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §5.1, Theorem 5.1.8, printed p. 74 / PDF p. 100; projection convention printed p. 71 / PDF p. 97; finite-convex-hull convention §3.1, printed p. 31 / PDF p. 51; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace Grunbaum2003

/-- Grünbaum (2003), §5.1, Theorem 8 (5.1.8), printed p.74 / PDF100,
Klee's recognition criterion. The ambient dimension admits 2 ≤ j < d.
A polytope is a finite convex hull, with the same encoding as the local
`polytope_iff_bounded_polyhedral`; empty and lower-dimensional sets are allowed.
Projections are all surjective affine maps onto j-dimensional coordinate space:
§5.1 p.71 defines projection as singular affine image. Surjectivity fixes the
rank at j, and j < d ensures singularity. No closedness hypothesis is added.
Statement only. -/
theorem polytope_iff_polytope_projections (d : ℕ) (hd : 3 ≤ d)
    (K : Set (Fin d → ℝ)) (hbounded : Bornology.IsBounded K)
    (hconvex : Convex ℝ K) :
    (∃ V : Set (Fin d → ℝ), V.Finite ∧ K = convexHull ℝ V) ↔
      ∃ j : ℕ, 2 ≤ j ∧ j < d ∧
        ∀ f : (Fin d → ℝ) →ᵃ[ℝ] (Fin j → ℝ), Function.Surjective f →
          ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' K = convexHull ℝ W := by sorry

end Grunbaum2003
