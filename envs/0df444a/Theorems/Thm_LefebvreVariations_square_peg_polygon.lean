-- Prove2me | Theorems.Thm_LefebvreVariations_square_peg_polygon
-- name    : LefebvreVariations.square_peg_polygon
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:37:07.006065+00:00
-- url     : https://prove2.me/theorems/a3114c35-f0a7-4cab-aaa4-a2fa028b2862
-- title:
--   Lefebvre's variations, No. 192 — on a theme by Toeplitz: every polygonal Jordan curve has an inscribed square
-- statement:
--   Let $S$ be a finite set of segments $[u,v]\subset\mathbb{R}^2$ whose union $C=\bigcup_{[u,v]\in S}[u,v]$ is a Jordan curve (a simple closed polygon, possibly with collinear consecutive edges). Then $C$ contains the four vertices $p_1,p_2,p_3,p_4$ of a (non-degenerate) square:
--   $$\exists\,p_1,p_2,p_3,p_4\in C:\quad p_1p_2p_3p_4\ \text{is a square}.$$
--
--   This is the square peg conjecture restricted to polygonal Jordan curves. A polygonal Jordan curve is locally a graph over a line near each of its points (at a vertex, the two edges can be separated by a linear functional), hence is locally monotone in Stromquist's sense, and Stromquist's theorem of 1989 gives an inscribed square. Polygons were already a classical case in the early work of Emch.
--
--   **Formalization Note** `Plane = EuclideanSpace ℝ (Fin 2)`; the curve is the set `⋃ s ∈ S, segment ℝ s.1 s.2` for a `Finset (Plane × Plane)` of endpoint pairs, and `Schoenflies.IsJordanCurve` (from the platform's `Def_SchoenfliesCurveCore`) says it is the image of a loop injective on `[0,1)`. `SquarePeg.IsSquare` is the platform's non-degenerate square predicate. Degenerate segments (equal endpoints) are allowed in `S` and harmless.
--
--   **Why this is a variation.** Special case of the open platform problem SquarePeg.square_peg_conjecture where the Jordan curve is a finite union of segments (a simple closed polygon). It is also a special case of SquarePeg.stromquist_locally_monotone (open on the platform): a polygon is locally monotone, since at every point its two incident rays are separated by a linear functional.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: SquarePeg.square_peg_conjecture (open on the platform, all Jordan curves); a polygonal Jordan curve is a special case, and it is also a special case of SquarePeg.stromquist_locally_monotone (open on the platform) because a polygon is locally monotone (checked by hand: at each point the curve is two rays, separated by a linear functional).
--   Source: W. Stromquist, 'Inscribed squares and square-like quadrilaterals in closed curves', Mathematika 36 (1989), 187-197 (cited from memory); A. Emch for polygons, early 20th century (cited from memory, title not verified); survey: B. Matschke, Notices of the AMS 61 (2014) (cited from memory).

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes

set_option autoImplicit false

open Schoenflies

namespace LefebvreVariations

/-- Square peg for polygons: a Jordan curve that is a finite union of segments has an inscribed
square. A special case of `SquarePeg.square_peg_conjecture`, and of Stromquist's theorem
`SquarePeg.stromquist_locally_monotone` since such a curve is locally monotone. -/
theorem square_peg_polygon (S : Finset (Plane × Plane))
    (hC : IsJordanCurve (⋃ s ∈ S, segment ℝ s.1 s.2)) :
    ∃ p1 p2 p3 p4 : Plane,
      p1 ∈ (⋃ s ∈ S, segment ℝ s.1 s.2) ∧ p2 ∈ (⋃ s ∈ S, segment ℝ s.1 s.2) ∧
      p3 ∈ (⋃ s ∈ S, segment ℝ s.1 s.2) ∧ p4 ∈ (⋃ s ∈ S, segment ℝ s.1 s.2) ∧
      SquarePeg.IsSquare p1 p2 p3 p4 := by
  sorry

end LefebvreVariations
