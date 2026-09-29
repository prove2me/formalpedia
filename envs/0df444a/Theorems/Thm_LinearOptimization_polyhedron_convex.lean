-- Prove2me | Theorems.Thm_LinearOptimization_polyhedron_convex
-- name    : LinearOptimization.polyhedron_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T13:53:56.492397+00:00
-- url     : https://prove2.me/theorems/a1d986ba-4abd-44fa-b794-2954f48a7bb7
-- title:
--   Convexity of polyhedra
-- statement:
--   **(Theorem 2.1, part (b) formalized)** Every polyhedron is a convex set.
--
--   The book's full statement:
--
--   - **(a)** The intersection of convex sets is convex.
--   - **(b)** Every polyhedron is a convex set.
--   - **(c)** A convex combination of a finite number of elements of a convex set also belongs to that set.
--   - **(d)** The convex hull of a finite number of vectors is a convex set.
--
--   *Encoding:* Parts (a), (c), (d) are Mathlib (`Convex.inter`/`convex_iInter`, `Convex.sum_mem`, `convex_convexHull`); the item is part (b) for the polyhedron Def of this mission.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 2.1, p. 44

import Mathlib.Analysis.Convex.Basic
import Definitions.Def_Polyhedron


/-- **B&T Theorem 2.1(b) (p. 44).** Every polyhedron `{x | Ax ≥ b}` is a
convex set. -/

theorem LinearOptimization.polyhedron_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Convex ℝ (polyhedron A b) := by sorry
