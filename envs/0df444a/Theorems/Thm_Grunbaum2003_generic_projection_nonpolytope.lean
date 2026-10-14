-- Prove2me | Theorems.Thm_Grunbaum2003_generic_projection_nonpolytope
-- name    : Grunbaum2003.generic_projection_nonpolytope
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-12T04:13:24.658281+00:00
-- url     : https://prove2.me/theorems/adfc78ab-3e2b-447e-99ee-e37bed529008
-- title:
--   Lemma C deep core: generic projection of a non-polytope is not a polytope
-- statement:
--   Lemma C deep core (Klee 1959 / Grunbaum 2003, Section 5.1, proof of Theorem 8). Let K be a compact convex subset of R^d with infinitely many extreme points, d >= 3. Then for every 2 <= j < d there exists a surjective affine map f : R^d -> R^j whose image f(K) is not a polytope (i.e. not a finite convex hull). Proof idea: reduce to j = 2 -- a generic 2-plane projection of a non-polytope body has infinitely many extreme points (the 'bad' directions identifying distinct extreme points form a countable union of proper algebraic subvarieties of the sphere, hence are meagre); for j > 2 compose with a linear embedding R^2 -> R^j. This is the missing deep input of the Klee recognition criterion decomposition (Grunbaum2003.klee_recognition_criterion), together with Grunbaum2003.projections_polytope_implies_closed and Grunbaum2003.compact_convex_nonpolytope_infinite_extreme.

import Mathlib

namespace Grunbaum2003

-- Klee (1959) / Grunbaum (2003), Section 5.1, proof of Theorem 8:
-- the generic-projection core of Lemma C. A compact convex K in R^d
-- (d >= 3) with infinitely many extreme points admits, for every
-- 2 <= j < d, a surjective affine map f : R^d -> R^j whose image is
-- not a polytope. Proof sketch: reduce to j = 2 -- a generic 2-plane
-- projection of a non-polytope body has infinitely many extreme
-- points (the "bad" directions identifying extreme points form a
-- countable union of proper algebraic subvarieties of the sphere,
-- hence are meagre); for j > 2 compose with a linear embedding
-- R^2 -> R^j.
theorem generic_projection_nonpolytope (d : ℕ) (hd : 3 ≤ d)
    (K : Set (Fin d → ℝ))
    (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hext : (K.extremePoints ℝ).Infinite)
    (j : ℕ) (hj2 : 2 ≤ j) (hjd : j < d) :
    ∃ f : (Fin d → ℝ) →ᵃ[ℝ] (Fin j → ℝ), Function.Surjective f ∧
      ¬ ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' K = convexHull ℝ W := by
  sorry

end Grunbaum2003
