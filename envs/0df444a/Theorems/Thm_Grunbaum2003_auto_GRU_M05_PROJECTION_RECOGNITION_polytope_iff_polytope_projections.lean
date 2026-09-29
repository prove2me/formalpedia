-- Prove2me | Theorems.Thm_Grunbaum2003_auto_GRU_M05_PROJECTION_RECOGNITION_polytope_iff_polytope_projections
-- name    : Grunbaum2003.auto_GRU_M05_PROJECTION_RECOGNITION_polytope_iff_polytope_projections
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T19:05:37.772602+00:00
-- url     : https://prove2.me/theorems/39044f07-20f4-472e-8561-411a5da96552
-- title:
--   Theorem 5.1.8 — Recognition from projections
-- statement:
--   For d ≥ 3, let K be any bounded convex subset of real d-dimensional space. Then K is the convex hull of a finite set if and only if there exists an integer j with 2 ≤ j < d such that every surjective affine map from real d-space to real j-space sends K to the convex hull of a finite set. The dimension j is fixed before quantifying over maps; the finite hull witness can depend on the map. Empty and lower-dimensional sets are included; closedness is not assumed.
-- source:
--   Branko Grünbaum, Convex Polytopes, second edition, Springer, 2003, §5.1 Theorem 8 (5.1.8), printed p.74 / source.pdf page 100; projection convention printed p.71 / PDF97; finite-convex-hull convention §3.1 printed p.31 / PDF51.

import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace Grunbaum2003

theorem auto_GRU_M05_PROJECTION_RECOGNITION_polytope_iff_polytope_projections (d : ℕ) (hd : 3 ≤ d)
    (K : Set (Fin d → ℝ)) (hbounded : Bornology.IsBounded K)
    (hconvex : Convex ℝ K) :
    (∃ V : Set (Fin d → ℝ), V.Finite ∧ K = convexHull ℝ V) ↔
      ∃ j : ℕ, 2 ≤ j ∧ j < d ∧
        ∀ f : (Fin d → ℝ) →ᵃ[ℝ] (Fin j → ℝ), Function.Surjective f →
          ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' K = convexHull ℝ W := by sorry


end Grunbaum2003
