-- Prove2me | Theorems.Thm_LefebvreVariations_chromatic_number_plane_at_least_4
-- name    : LefebvreVariations.chromatic_number_plane_at_least_4
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T23:10:33.364232+00:00
-- url     : https://prove2.me/theorems/2252b289-ee60-46dd-a14f-8851a7562209
-- title:
--   Lefebvre's variations, No. 34 — on a theme by Hadwiger and Nelson: the plane cannot be 3-coloured (the Moser spindle)
-- statement:
--   This is the first non-trivial lower bound for the chromatic number of the plane.
--
--   Colour every point of the Euclidean plane with one of three colours. Then there are two points at distance exactly $1$ that have the same colour; that is, $\chi(\mathbb R^2)\ge4$.
--
--   The proof uses the Moser spindle: seven points and eleven unit distances. If two points $X,Y$ are at distance $\sqrt3$, they are the two far tips of two unit rhombi, so $X,Y$ and the two other vertices $P,Q$ satisfy $XP=XQ=YP=YQ=PQ=1$; with only three colours, $X$ and $Y$ must take the same colour. Applying this to $O$, $Y=(\frac{\sqrt{11}}2,\frac12)$ and $Z=(\frac{\sqrt{11}}2,-\frac12)$, both $Y$ and $Z$ have the colour of $O$, but $YZ=1$.
--
--   The Hadwiger–Nelson problem asks for the exact value of $\chi(\mathbb R^2)$, known to lie between $5$ and $7$; this is the classical first step, $\chi(\mathbb R^2)\ge4$.
--
--   **Formalization Note** Points are pairs of reals, and two points are at unit distance when the squared Euclidean distance equals $1$.
--
--   **Why this is a variation.** This varies the Hadwiger–Nelson problem, the open question of the chromatic number $\chi(\mathbb{R}^2)$ of the plane for the unit-distance graph. It is the first non-trivial size: no 3-colouring of the plane avoids a monochromatic pair at distance 1, so $\chi(\mathbb{R}^2)\ge 4$, witnessed by the 7-point Moser spindle. It is a weaker, classical rung below the platform's $\chi\ge 5$ and fixes the bottom of the ladder of lower bounds for the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   L. Moser and W. Moser, Solution to Problem 10, Canad. Math. Bull. 4 (1961), 187–189 (the Moser spindle; page range cited from memory). The problem: E. Nelson (1950) and H. Hadwiger (1945), see A. Soifer, The Mathematical Coloring Book, Springer, 2009. Parent problem: chromatic_number_plane_at_least_5 and hadwiger_nelson_conjecture.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Hadwiger–Nelson, the first non-trivial size: the plane has no proper 3-colouring for the
unit-distance relation, i.e. `χ(ℝ²) ≥ 4`.  Witness: the Moser spindle (7 points, 11 unit
distances; two unit rhombi sharing a vertex, one rotated by `arccos (5/6)` so that their far tips
are at distance 1).  Same shape as `chromatic_number_plane_at_least_5`, with `Fin 3`.
Moser & Moser, "Solution to problem 10", Canad. Math. Bull. 4 (1961), 187–189. -/
theorem chromatic_number_plane_at_least_4 :
    ∀ (col : ℝ × ℝ → Fin 3),
      ∃ p q : ℝ × ℝ, (p.1 - q.1)^2 + (p.2 - q.2)^2 = 1 ∧ col p = col q := by
  sorry

end LefebvreVariations
