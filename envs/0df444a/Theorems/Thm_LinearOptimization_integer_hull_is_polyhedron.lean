-- Prove2me | Theorems.Thm_LinearOptimization_integer_hull_is_polyhedron
-- name    : LinearOptimization.integer_hull_is_polyhedron
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-09T16:00:23.407315+00:00
-- url     : https://prove2.me/theorems/e81ba535-d81b-41b8-b629-65ee16b9b949
-- title:
--   The integer hull $CH(X)$ is a polyhedron
-- statement:
--   **(Theorem 11.3 — Bertsimas & Tsitsiklis, p. 496.)** We assume that the system of linear inequalities $Dx \ge d$ has a feasible solution, and that the matrix $D$ and the vector $d$ have integer entries. Let
--
--   $$X = \{x\ \text{integer} \mid Dx \ge d\}.$$
--
--   Then $CH(X)$, the convex hull of $X$, is a polyhedron.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 11.3, p. 496

import Mathlib.Analysis.Convex.Hull
import Definitions.Def_LinearOptimization_LagrangeanDual


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 11.3 (p. 496).** The convex hull of the integer points
of a polyhedron with integer data is a polyhedron: if `Dx ≥ d` is
feasible and `D`, `d` are integer, then `CH({x integer | Dx ≥ d})` equals
`{x | Fx ≥ f}` for some finite real system `(F, f)`. -/

theorem LinearOptimization.integer_hull_is_polyhedron {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℤ) (d : Fin m → ℤ)
    (hfeas : (polyhedron (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ))).Nonempty) :
    ∃ (k : ℕ) (F : Matrix (Fin k) (Fin n) ℝ) (f : Fin k → ℝ),
      convexHull ℝ
          (lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ))) =
        polyhedron F f := by
  sorry
