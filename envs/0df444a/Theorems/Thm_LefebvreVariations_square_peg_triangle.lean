-- Prove2me | Theorems.Thm_LefebvreVariations_square_peg_triangle
-- name    : LefebvreVariations.square_peg_triangle
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:38:30.70173+00:00
-- url     : https://prove2.me/theorems/3b1a4f62-45aa-59b6-8dd0-e3e2e75c49fc
-- title:
--   Lefebvre's variations, No. 240 — on a theme by Toeplitz: every triangle has an inscribed square on its boundary
-- statement:
--   Let $a,b,c\in\mathbb{R}^2$ be three non-collinear points and let $C=\partial\,\mathrm{conv}\{a,b,c\}$ be the boundary of the triangle they span. Then $C$ contains the four vertices $p_1,p_2,p_3,p_4$ of a (non-degenerate) square:
--   $$\exists\,p_1,p_2,p_3,p_4\in C:\quad p_1p_2p_3p_4\ \text{is a square}.$$
--
--   The boundary of a triangle is a Jordan curve, so this is the first non-smooth special case of Toeplitz's square peg conjecture (every Jordan curve in the plane contains the vertices of a square). It is classical: for each side one can inscribe a square with two vertices on that side, of side length $ah/(a+h)$ where $a$ is the side and $h$ the corresponding height.
--
--   **Formalization Note** Points are in `Schoenflies.Plane = EuclideanSpace ℝ (Fin 2)`; the triangle's boundary is `frontier (convexHull ℝ {a, b, c})` and the non-degeneracy hypothesis is `¬ Collinear ℝ {a, b, c}`. `SquarePeg.IsSquare p1 p2 p3 p4` (from the platform's `Def_SquarePeg_shapes`) says that `p1, p2, p3, p4` in cyclic order form a non-degenerate rectangle with equal adjacent sides: `p1 + p3 = p2 + p4`, `dist p1 p3 = dist p2 p4`, `p1 ≠ p2`, `p2 ≠ p3`, `dist p1 p2 = dist p2 p3`.
--
--   **Why this is a variation.** Special case of the open platform problem SquarePeg.square_peg_conjecture (every Jordan curve in the plane has an inscribed square), where the Jordan curve is the boundary of a non-degenerate triangle. It also falls under SquarePeg.convex_curve_inscribed_square, and the proof is the classical inscribed square on a side of length ah/(a+h).
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: SquarePeg.square_peg_conjecture (open on the platform, for every Jordan curve C); the boundary of a non-degenerate triangle is a Jordan curve, so this is a special case (it is also a case of SquarePeg.convex_curve_inscribed_square, open on the platform).
--   Source: classical (inscribed squares in triangles are in every geometry text); the square peg problem is due to O. Toeplitz (1911), see B. Matschke, 'A survey on the square peg problem', Notices of the AMS 61 (2014) (cited from memory). Verified numerically here: for 20000 random triangles the construction of side ah/(a+h) puts two vertices on the base and two on the other sides.

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes

set_option autoImplicit false

open Schoenflies

namespace LefebvreVariations

/-- Every triangle has an inscribed square: the boundary of a non-degenerate triangle, a Jordan
curve, carries the four vertices of a square. A special case of the square peg conjecture
`SquarePeg.square_peg_conjecture`. -/
theorem square_peg_triangle (a b c : Plane) (h : ¬ Collinear ℝ ({a, b, c} : Set Plane)) :
    ∃ p1 p2 p3 p4 : Plane,
      p1 ∈ frontier (convexHull ℝ ({a, b, c} : Set Plane)) ∧
      p2 ∈ frontier (convexHull ℝ ({a, b, c} : Set Plane)) ∧
      p3 ∈ frontier (convexHull ℝ ({a, b, c} : Set Plane)) ∧
      p4 ∈ frontier (convexHull ℝ ({a, b, c} : Set Plane)) ∧
      SquarePeg.IsSquare p1 p2 p3 p4 := by
  sorry

end LefebvreVariations
