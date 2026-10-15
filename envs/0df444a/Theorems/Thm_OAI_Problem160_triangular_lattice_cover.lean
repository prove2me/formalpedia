-- Prove2me | Theorems.Thm_OAI_Problem160_triangular_lattice_cover
-- name    : OAI.Problem160.triangular_lattice_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T17:41:00.713643+00:00
-- url     : https://prove2.me/theorems/646e2fd3-f4ea-487b-8ad0-f119aed9312a
-- title:
--   Every point of the plane lies within distance $1/\sqrt{3}$ of the unit triangular lattice
-- statement:
--   Consider the triangular lattice of unit spacing in the plane, $\Lambda=\{m\,e_1+n\,e_2:\ m,n\in\mathbb{Z}\}$ with $e_1=(1,0)$ and $e_2=\bigl(\tfrac12,\tfrac{\sqrt3}{2}\bigr)$, so that $m\,e_1+n\,e_2=\bigl(m+\tfrac n2,\ \tfrac{\sqrt3}{2}\,n\bigr)$. For all real numbers $x$ and $y$ there exist integers $m$ and $n$ such that
--   $$\Bigl(x-\bigl(m+\tfrac n2\bigr)\Bigr)^2+\Bigl(y-\tfrac{\sqrt3}{2}\,n\Bigr)^2\le\frac13 .$$
--   Equivalently, every point $(x,y)$ of the plane lies within Euclidean distance $1/\sqrt3$ of some point of $\Lambda$: the closed disks of radius $1/\sqrt3$ centered at the lattice points cover the plane.
--
--   The radius $1/\sqrt3$ is the circumradius of the unit equilateral triangles formed by neighboring lattice points, and it cannot be decreased: the center $\bigl(\tfrac12,\tfrac{1}{2\sqrt3}\bigr)$ of the triangle with vertices $0$, $e_1$, $e_2$ is at distance exactly $1/\sqrt3$ from these three vertices and farther from all other lattice points. After scaling by $\tfrac45$, this covering bound is the geometric input of the seven-coloring of the plane: every point lies within $\tfrac{4}{5\sqrt3}<\tfrac{7}{15}$ of the scaled lattice.
--
--   **Formalization Note** The statement is written in coordinates, with real numbers $x,y$ and the lattice point $\bigl(m+n/2,\ \sqrt3\,n/2\bigr)$, where $\sqrt3$ is `Real.sqrt 3`; no vector-space structure is used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/PlaneColoring/Covering.lean#L45-L91

import Mathlib
import Definitions.Def_PlaneColoring
import Definitions.Def_OAI_Geometry_PlaneColoring_Lattice
import Definitions.Def_OAI_Geometry_PlaneColoring_Basic
import Definitions.Def_OAI_Geometry_PlaneColoring_Metric

open OAI OAI.Problem160

theorem OAI.Problem160.triangular_lattice_cover (x y : ℝ) :
    ∃ m n : ℤ,
      (x - ((m : ℝ) + (n : ℝ) / 2)) ^ 2 +
        (y - Real.sqrt 3 * (n : ℝ) / 2) ^ 2 ≤ 1 / 3 := by sorry
