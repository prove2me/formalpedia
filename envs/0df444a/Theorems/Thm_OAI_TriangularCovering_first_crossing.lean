-- Prove2me | Theorems.Thm_OAI_TriangularCovering_first_crossing
-- name    : OAI.TriangularCovering.first_crossing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:45:32.171451+00:00
-- url     : https://prove2.me/theorems/284b1ed2-2f78-46cc-93a3-3fa25788cc66
-- title:
--   Discrete intermediate value theorem: a finite sequence crosses every intermediate level
-- statement:
--   Let $N\ge1$ be a natural number, let $f:\mathbb{N}\to\mathbb{R}$ be an arbitrary function, and let $z\in\mathbb{R}$ satisfy $f(0)\le z\le f(N)$. Then there is an index $j$ with $0\le j<N$ such that
--   $$
--   f(j)\le z\le f(j+1).
--   $$
--
--   This is a discrete intermediate value theorem: no monotonicity of $f$ is assumed, and the conclusion locates a pair of consecutive indices whose values enclose $z$. In the covering of the tetrahedron by tilted triangular cylinders it is used to find, for a given point, a mesh cell $[m_j,m_{j+1}]$ of $[-1,1]$ whose secant-corrected angular sector contains that point.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean#L115-L129

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.first_crossing {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ) (z : ℝ)
    (h0 : f 0 ≤ z) (hN' : z ≤ f N) :
    ∃ j : ℕ, j < N ∧ f j ≤ z ∧ z ≤ f (j + 1) := by sorry
