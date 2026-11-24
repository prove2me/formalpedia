-- Prove2me | Theorems.Thm_LefebvreVariations_kissing_number_eight_lower
-- name    : LefebvreVariations.kissing_number_eight_lower
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T23:25:13.224536+00:00
-- url     : https://prove2.me/theorems/093407c8-1f61-4ebd-aa51-0893c162f6e8
-- title:
--   Lefebvre's variations: the kissing number in dimension 8 is at least 240
-- statement:
--   This is the lower bound $240\le\tau_8$ for the kissing number in dimension $8$.
--
--   The kissing number $\tau_d$ is the maximum number of non-overlapping unit balls that can touch a central unit ball in $\mathbb R^d$. Then
--
--   $$
--   \tau_8\ \ge\ 240 .
--   $$
--
--   A configuration is given by the $240$ roots of $E_8$, written with doubled coordinates: the $112$ vectors $\pm2e_i\pm2e_j$ and the $128$ vectors $(\pm1)^8$ with an even number of minus signs. They all have squared length $8$ and any two distinct ones have inner product at most $4$, that is, angle at least $60^\circ$; scaled to unit length they are the centres of the touching balls.
--
--   The value $240$ is exact (Odlyzko–Sloane and Levenshtein, 1979); the statement here is the elementary lower bound from the explicit configuration.
--
--   **Formalization Note** The statement is in the mission's `KissingNumber` formulation, with the kissing number valued in the extended naturals.
-- source:
--   Explicit configuration: J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and Groups, 3rd ed., Springer, 1999, Chapter 1 and Chapter 4 (root systems D_3, D_4, E_8 and their kissing configurations). Exact values: K. Schütte and B. L. van der Waerden, Das Problem der dreizehn Kugeln, Math. Ann. 125 (1953), 325–334 (d = 3); O. R. Musin, The kissing number in four dimensions, Ann. of Math. 168 (2008), 1–32 (d = 4); A. M. Odlyzko and N. J. A. Sloane, New bounds on the number of unit spheres that can touch a unit sphere in n dimensions, J. Combin. Theory Ser. A 26 (1979), 210–214, and V. I. Levenshtein, 1979 (d = 8). Parent problem: KissingNumber.kissing_number_eight.

import Definitions.Def_KissingNumber

set_option autoImplicit false

namespace LefebvreVariations

open KissingNumber

/-- Lower half of `KissingNumber.kissing_number_eight`: `240 ≤ τ(8)`, by an explicit configuration. -/
theorem kissing_number_eight_lower : (240 : ℕ∞) ≤ kissingNumber 8 := by
  sorry

end LefebvreVariations
