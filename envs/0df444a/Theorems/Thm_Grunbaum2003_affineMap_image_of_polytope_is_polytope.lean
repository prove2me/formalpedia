-- Prove2me | Theorems.Thm_Grunbaum2003_affineMap_image_of_polytope_is_polytope
-- name    : Grunbaum2003.affineMap_image_of_polytope_is_polytope
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-08T16:17:20.680379+00:00
-- url     : https://prove2.me/theorems/1e4719ab-0daa-4010-88ce-0cee5364cf4a
-- title:
--   Affine image of a polytope is a polytope
-- statement:
--   Grünbaum (2003), §5.1, Theorem 8 (5.1.8), forward direction. The affine image of a polytope — a finite convex hull — is again a polytope, i.e. a finite convex hull. This is the elementary direction of the projection-recognition theorem (the reverse, Perles' recognition criterion, is deep and parked). Follows from: a convex combination maps to a convex combination, and the affine image of a finite set is finite.

import Mathlib

namespace Grunbaum2003

/-- Grünbaum (2003), §5.1, Theorem 8 (5.1.8), forward direction:
    the affine image of a polytope (a finite convex hull) is
again a polytope, i.e. a finite convex hull. The reverse direction
(Perles' recognition criterion) is deep and parked. -/
theorem affineMap_image_of_polytope_is_polytope :
    ∀ (d j : ℕ) (V : Set (Fin d → ℝ)), V.Finite →
      ∀ f : (Fin d → ℝ) →ₐ[ℝ] (Fin j → ℝ),
        ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' (convexHull ℝ V) = convexHull ℝ W := by
  sorry

end Grunbaum2003
