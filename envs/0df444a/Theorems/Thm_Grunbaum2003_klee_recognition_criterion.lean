-- Prove2me | Theorems.Thm_Grunbaum2003_klee_recognition_criterion
-- name    : Grunbaum2003.klee_recognition_criterion
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-10T04:03:45.741188+00:00
-- url     : https://prove2.me/theorems/4f434a84-9236-42b8-ae0d-cbf466e77fed
-- title:
--   Klee's recognition criterion: bounded convex set with polytope projections is a polytope (Lemma C)
-- statement:
--   Grunbaum (2003), §5.1, Theorem 8 (5.1.8), reverse direction, Lemma C (Klee's recognition criterion, the deep core). A bounded convex set K in R^d (d ≥ 3) for which there exists 2 ≤ j < d such that every surjective affine map R^d → R^j sends K to a polytope (a finite convex hull) is itself a polytope (a finite convex hull). With Lemma A (closedness) K is compact, and with Lemma B (Krein–Milman) a compact convex non-polytope has infinitely many extreme points; the remaining deep step is a generic-projection argument turning those into a non-polytopal image, contradicting the hypothesis. This node states exactly the problem to be solved; the full recognition argument is parked.

import Mathlib

namespace Grunbaum2003

/-- Grunbaum (2003), §5.1, Theorem 8 (5.1.8), reverse direction — Lemma C (Klee's recognition
    criterion, the deep core): a bounded convex set K ⊂ ℝ^d (d ≥ 3) for which some 2 ≤ j < d
    has every surjective affine map ℝ^d → ℝ^j sending K to a finite convex hull (a polytope)
    is itself a finite convex hull (a polytope). With Lemma A (closedness) K is compact, and
    with Lemma B (Krein–Milman) a compact convex non-polytope has infinitely many extreme
    points; the remaining deep step is a generic-projection argument turning those into a
    non-polytopal image, contradicting the hypothesis. This node states exactly the problem
    to be solved; the full recognition argument is parked. -/
theorem klee_recognition_criterion (d : ℕ) (hd : 3 ≤ d)
    (K : Set (Fin d → ℝ)) (hbounded : Bornology.IsBounded K)
    (hconvex : Convex ℝ K)
    (hproj : ∃ j : ℕ, 2 ≤ j ∧ j < d ∧
      ∀ f : (Fin d → ℝ) →ᵃ[ℝ] (Fin j → ℝ), Function.Surjective f →
        ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' K = convexHull ℝ W) :
    ∃ V : Set (Fin d → ℝ), V.Finite ∧ K = convexHull ℝ V := by
  sorry

end Grunbaum2003
