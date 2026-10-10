-- Prove2me | Theorems.Thm_Grunbaum2003_projections_polytope_implies_closed
-- name    : Grunbaum2003.projections_polytope_implies_closed
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-09T20:13:41.69099+00:00
-- url     : https://prove2.me/theorems/2af5a585-2fd5-44ab-a523-d30b4fa91b31
-- title:
--   Bounded convex set with polytope projections is closed (Lemma A)
-- statement:
--   Grunbaum (2003), §5.1, Theorem 8 (5.1.8), reverse direction, Lemma A (closedness step). A bounded convex set K in R^d (d ≥ 3) for which there exists 2 ≤ j < d such that every surjective affine map R^d → R^j sends K to a polytope (a finite convex hull) is closed. This is the first deep step of Perles' recognition criterion: the projection hypothesis must recover closedness of K before compactness (bounded + closed in finite dimensions) can be used; the full reverse direction is parked.

import Mathlib

namespace Grunbaum2003

/-- Grunbaum (2003), §5.1, Theorem 8 (5.1.8), reverse direction — Lemma A (closedness step):
    a bounded convex set K ⊂ ℝ^d (d ≥ 3) for which some 2 ≤ j < d has every surjective
    affine map ℝ^d → ℝ^j sending K to a finite convex hull (a polytope) is closed.
    Recovering closedness from the projection hypothesis is the first deep step of
    Perles' recognition criterion; the full reverse direction is parked. -/
theorem projections_polytope_implies_closed (d : ℕ) (hd : 3 ≤ d)
    (K : Set (Fin d → ℝ)) (hbounded : Bornology.IsBounded K)
    (hconvex : Convex ℝ K)
    (hproj : ∃ j : ℕ, 2 ≤ j ∧ j < d ∧
      ∀ f : (Fin d → ℝ) →ᵃ[ℝ] (Fin j → ℝ), Function.Surjective f →
        ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' K = convexHull ℝ W) :
    IsClosed K := by
  sorry

end Grunbaum2003
