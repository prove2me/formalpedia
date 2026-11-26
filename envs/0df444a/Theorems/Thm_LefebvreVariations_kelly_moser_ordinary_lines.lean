-- Prove2me | Theorems.Thm_LefebvreVariations_kelly_moser_ordinary_lines
-- name    : LefebvreVariations.kelly_moser_ordinary_lines
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:52:54.057242+00:00
-- url     : https://prove2.me/theorems/77557316-3359-5bbd-9057-8a238b2677bc
-- title:
--   Lefebvre's variations, No. 113 — on a theme by Dirac and Motzkin: the Kelly–Moser bound on ordinary lines
-- statement:
--   Let $S\subset\mathbb{R}^2$ be a finite set of $n$ points not all on one line. An *ordinary line* of $S$ is a line containing exactly two points of $S$. Then $S$ determines at least $3n/7$ ordinary lines:
--   $$
--   7\cdot\#\{\text{ordinary lines of }S\}\;\ge\;3n.
--   $$
--
--   This is the Kelly–Moser theorem, a quantitative form of the Sylvester–Gallai theorem. The Dirac–Motzkin conjecture asserts at least $n/2$ ordinary lines for $n$ large; this was proved for large $n$ by Green and Tao, and the sharp constant for small $n$ is still not settled in general. The bound $3n/7$ is attained for $n=7$.
--
--   **Formalization Note** `S : Finset (EuclideanSpace ℝ (Fin 2))` with `¬ Collinear ℝ ↑S`. A line is identified with the pair of points of `S` it carries: the ordinary lines are counted as the `T ∈ S.powersetCard 2` such that for every `c ∈ S \ T` the set `insert c T` is not collinear. The conclusion is `3 * S.card ≤ 7 * #(ordinary pairs)`, an inequality of natural numbers; classical decidability is used for the filter.
--
--   **Why this is a variation.** Partial result towards the Dirac-Motzkin conjecture on ordinary lines (n points, not all collinear, determine at least n/2 ordinary lines for n large; proved for large n by Green and Tao). This is the Kelly-Moser bound 3n/7, sharp for n = 7. No entry for the conjecture was found on the platform by keyword search, so there is no platform parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): the Dirac-Motzkin conjecture on ordinary lines (at least n/2 ordinary lines for n points not all collinear, n large); no entry found on the platform by keyword search (the platform has the Sylvester-Gallai theorem itself, ProofsInTheBook.Chapter10.euclidean_sylvester_gallai, Proved). This statement is the Kelly-Moser partial result.
--   Source (verified by search): L. M. Kelly and W. O. J. Moser, 'On the number of ordinary lines determined by n points', Canad. J. Math. 10 (1958), 210-219 (bound 3n/7, sharp for n = 7 and 8). Context: Csima and Sawyer improved the constant to 6n/13 for n > 7 (year cited from memory); B. Green and T. Tao, 'On sets defining few ordinary lines', Discrete Comput. Geom. 50 (2013), 409-468 (verified).
--   Boundary check (exact integer arithmetic): the 7 points (0,0),(6,0),(0,6),(3,0),(0,3),(3,3),(2,2) (triangle, side midpoints, centroid) have exactly 3 ordinary lines, so 3n/7 = 3 is attained; 20000 random small integer sets gave no violation.

import Mathlib

set_option autoImplicit false

open Classical

namespace LefebvreVariations

/-- The Kelly–Moser bound towards the Dirac–Motzkin conjecture: `n` points of the plane, not all
collinear, determine at least `3n/7` ordinary lines. An ordinary line is counted as the pair of
points of `S` it contains, and contains no third point of `S`. -/
theorem kelly_moser_ordinary_lines (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : ¬ Collinear ℝ (↑S : Set (EuclideanSpace ℝ (Fin 2)))) :
    3 * S.card ≤ 7 * ((S.powersetCard 2).filter (fun T =>
      ∀ c ∈ S, c ∉ T → ¬ Collinear ℝ (↑(insert c T) : Set (EuclideanSpace ℝ (Fin 2))))).card := by
  sorry

end LefebvreVariations
