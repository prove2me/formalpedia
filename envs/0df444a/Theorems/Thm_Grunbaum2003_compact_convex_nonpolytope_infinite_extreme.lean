-- Prove2me | Theorems.Thm_Grunbaum2003_compact_convex_nonpolytope_infinite_extreme
-- name    : Grunbaum2003.compact_convex_nonpolytope_infinite_extreme
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-10T00:06:35.809483+00:00
-- url     : https://prove2.me/theorems/224054d5-0471-4884-9f01-38fd1c0d574d
-- title:
--   Compact convex non-polytope has infinitely many extreme points (Lemma B)
-- statement:
--   Grunbaum (2003), §5.1, Theorem 8 (5.1.8), reverse direction, Lemma B (Krein–Milman step). A compact convex set K in R^d that is not a finite convex hull (not a polytope) has infinitely many extreme points. Route: Krein–Milman (Mathlib's closure_convexHull_extremePoints) presents K as the closure of the convex hull of its extreme points, so a finite extreme-point set would make K a finite hull, contradicting the hypothesis. This feeds Lemma C (Klee's recognition criterion); the full reverse direction is parked.

import Mathlib

namespace Grunbaum2003

/-- Grunbaum (2003), §5.1, Theorem 8 (5.1.8), reverse direction — Lemma B (Krein–Milman step):
    a compact convex set K ⊂ ℝ^d that is NOT a finite convex hull (not a polytope) has infinitely
    many extreme points. Route: Krein–Milman (Mathlib's closure_convexHull_extremePoints) says K
    is the closure of the convex hull of its extreme points, so finitely many extreme points
    would make K a finite hull — contradiction. Feeds Lemma C (Klee's recognition criterion). -/
theorem compact_convex_nonpolytope_infinite_extreme (d : ℕ)
    (K : Set (Fin d → ℝ)) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K)
    (hnotpoly : ¬ ∃ V : Set (Fin d → ℝ), V.Finite ∧ K = convexHull ℝ V) :
    (K.extremePoints ℝ).Infinite := by
  sorry

end Grunbaum2003
