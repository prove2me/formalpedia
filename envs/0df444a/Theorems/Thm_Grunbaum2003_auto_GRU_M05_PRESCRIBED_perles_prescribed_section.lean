-- Prove2me | Theorems.Thm_Grunbaum2003_auto_GRU_M05_PRESCRIBED_perles_prescribed_section
-- name    : Grunbaum2003.auto_GRU_M05_PRESCRIBED_perles_prescribed_section
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T19:05:24.870985+00:00
-- url     : https://prove2.me/theorems/c8b6f3ca-d17d-42eb-a3a6-b625cb865402
-- title:
--   Theorem 5.1.10 — Simplex sections through a prescribed interior point
-- statement:
--   For all natural d and k, let P be a full-dimensional nonempty polytope in R^d with at most k+1 facets. For every k-simplex T in R^k and every p in its interior, there is a d-dimensional affine flat L containing p and an injective real affine map A from R^d onto L such that A(P) = T ∩ L. For d=0 the facet allowance is automatic.
-- source:
--   Branko Grünbaum, Convex Polytopes, second edition, Springer (2003), §5.1, Theorem 10 (5.1.10), printed p.74 / source.pdf page 100. Section convention: printed p.71 / PDF page 97.

import Definitions.Def_auto_GRU_M05_PRESCRIBED_IsDPolytope
import Definitions.Def_auto_GRU_M05_PRESCRIBED_faceCount
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

set_option autoImplicit false

namespace Grunbaum2003

theorem auto_GRU_M05_PRESCRIBED_perles_prescribed_section (d k : ℕ)
    (P : Set (Fin d → ℝ)) (hP : auto_GRU_M05_PRESCRIBED_IsDPolytope P)
    (hfacets : (if d = 0 then 0 else auto_GRU_M05_PRESCRIBED_faceCount P (d - 1)) ≤ k + 1)
    (v : Fin (k + 1) → (Fin k → ℝ)) (hv : AffineIndependent ℝ v)
    (p : Fin k → ℝ) (hp : p ∈ interior (convexHull ℝ (Set.range v))) :
    ∃ L : AffineSubspace ℝ (Fin k → ℝ),
      p ∈ L ∧ Module.finrank ℝ L.direction = d ∧
      ∃ A : (Fin d → ℝ) →ᵃ[ℝ] (Fin k → ℝ),
        Function.Injective A ∧ Set.range A = (L : Set (Fin k → ℝ)) ∧
          A '' P = convexHull ℝ (Set.range v) ∩ (L : Set (Fin k → ℝ)) := by sorry

end Grunbaum2003
