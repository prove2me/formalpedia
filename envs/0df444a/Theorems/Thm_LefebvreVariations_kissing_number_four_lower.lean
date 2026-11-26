-- Prove2me | Theorems.Thm_LefebvreVariations_kissing_number_four_lower
-- name    : LefebvreVariations.kissing_number_four_lower
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T23:22:09.803056+00:00
-- url     : https://prove2.me/theorems/93baac16-9c61-4c7e-9b32-88cf8513c56d
-- title:
--   Lefebvre's variations, No. 48 — on a theme by Conway and Sloane: the kissing number in dimension 4 is at least 24
-- statement:
--   This is the lower bound $24\le\tau_4$ for the kissing number in dimension $4$.
--
--   The kissing number $\tau_d$ is the maximum number of non-overlapping unit balls that can touch a central unit ball in $\mathbb R^d$. Then
--
--   $$
--   \tau_4\ \ge\ 24 .
--   $$
--
--   A configuration is given by the $24$ vectors $\pm e_i\pm e_j$ ($i<j$) of the $D_4$ root system (the vertices of the $24$-cell): they all have squared length $2$ and any two distinct ones have inner product at most $1$, that is, angle at least $60^\circ$; scaled to unit length they are the centres of the touching balls.
--
--   The value $24$ is exact (Musin, 2008); the statement here is the elementary lower bound from the explicit configuration.
--
--   **Formalization Note** The statement is in the mission's `KissingNumber` formulation, with the kissing number valued in the extended naturals.
--
--   **Why this is a variation.** This varies the kissing number problem in dimension 4, which asks for $\tau(4)$. It is the lower half of the parent: $24\le\tau(4)$, realised by an explicit configuration of 24 unit vectors. Together with the matching upper bound it gives $\tau(4)=24$.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Explicit configuration: J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and Groups, 3rd ed., Springer, 1999, Chapter 1 and Chapter 4 (root systems D_3, D_4, E_8 and their kissing configurations). Exact values: K. Schütte and B. L. van der Waerden, Das Problem der dreizehn Kugeln, Math. Ann. 125 (1953), 325–334 (d = 3); O. R. Musin, The kissing number in four dimensions, Ann. of Math. 168 (2008), 1–32 (d = 4); A. M. Odlyzko and N. J. A. Sloane, New bounds on the number of unit spheres that can touch a unit sphere in n dimensions, J. Combin. Theory Ser. A 26 (1979), 210–214, and V. I. Levenshtein, 1979 (d = 8). Parent problem: KissingNumber.kissing_number_four.

import Definitions.Def_KissingNumber

set_option autoImplicit false

namespace LefebvreVariations

open KissingNumber

/-- Lower half of `KissingNumber.kissing_number_four`: `24 ≤ τ(4)`, by an explicit configuration. -/
theorem kissing_number_four_lower : (24 : ℕ∞) ≤ kissingNumber 4 := by
  sorry

end LefebvreVariations
