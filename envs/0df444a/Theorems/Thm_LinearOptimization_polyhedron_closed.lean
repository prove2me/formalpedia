-- Prove2me | Theorems.Thm_LinearOptimization_polyhedron_closed
-- name    : LinearOptimization.polyhedron_closed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T18:43:05.654403+00:00
-- url     : https://prove2.me/theorems/00c98cf7-7b73-44ef-9acd-b43230ea4032
-- title:
--   Closedness of polyhedra
-- statement:
--   **(Theorem 4.9)** Every polyhedron is closed.
--
--   (A set $S \subset \mathbb{R}^n$ is called *closed* if it has the following property: if $x^1, x^2, \dots$ is a sequence of elements of $S$ that converges to some $x \in \mathbb{R}^n$, then $x \in S$. Book proof: for $P = \{x \in \mathbb{R}^n \mid Ax \ge b\}$ and $x^k \to x^*$ with $Ax^k \ge b$, taking the limit gives $Ax^* \ge b$.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.9, p. 169

import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_Polyhedron


/-- **Bertsimas & Tsitsiklis, Theorem 4.9 (p. 169).** Every polyhedron `{x | Ax ≥ b}` is a
closed subset of `ℝⁿ`. -/

theorem LinearOptimization.polyhedron_closed {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    IsClosed (polyhedron A b) := by
  sorry
