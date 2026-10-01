-- Prove2me | Theorems.Thm_Grunbaum2003_affine_image_of_polytope_is_polytope
-- name    : Grunbaum2003.affine_image_of_polytope_is_polytope
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T17:44:24.210983+00:00
-- url     : https://prove2.me/theorems/ce966691-42c8-4272-8f01-642e1ebf97ba
-- title:
--   Affine image of a polytope is a polytope
-- statement:
--   Grünbaum (2003), §5.1, Theorem 8 (5.1.8), forward direction. The affine (linear) image of a polytope — a finite convex hull — is again a polytope, i.e. a finite convex hull. This is the elementary direction of the projection-recognition theorem (the reverse, Perles' recognition criterion, is deep and parked). Follows from: a convex combination maps to a convex combination, and the linear image of a finite set is finite.

import Mathlib

namespace Grunbaum2003

/-- Grünbaum (2003), §5.1, Theorem 8 (5.1.8), forward direction:
    the affine (linear) image of a polytope (a finite convex hull) is
again a polytope, i.e. a finite convex hull. The reverse direction
(Perles' recognition criterion) is deep and parked. -/
theorem affine_image_of_polytope_is_polytope :
    ∀ (d j : ℕ) (V : Set (Fin d → ℝ)), V.Finite →
      ∀ f : (Fin d → ℝ) →ₗ[ℝ] (Fin j → ℝ),
        ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' (convexHull ℝ V) = convexHull ℝ W := by
  sorry

end Grunbaum2003
