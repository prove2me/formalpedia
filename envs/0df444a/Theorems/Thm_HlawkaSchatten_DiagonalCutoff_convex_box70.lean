-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_convex_box70
-- name    : HlawkaSchatten.DiagonalCutoff.convex_box70
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T04:14:54.276926+00:00
-- url     : https://prove2.me/theorems/ed807fb6-72a3-4413-b7db-48a88ab47fd4
-- title:
--   Convexity of the triple deficit on the cutoff-70 entry box
-- statement:
--   For an exponent $p\ge 70$ and a height $K$ between $\frac{23}{50}p$ and $p$, the triple deficit is a convex function of the nine matrix entries on the cutoff-$70$ asymmetric box.
--
--   Let $p\ge 70$ and $\frac{23}{50}p\le K\le p$. On the set of $3\times 3$ real matrices whose diagonal entries lie in $[-\frac{219}{200},-\frac{5217}{7000}]$ and whose off-diagonal entries lie in $[\frac{5217}{7000},\frac{219}{200}]$, the map
--
--   $$
--   X\mapsto K\sum_{j<k}\big(\|X_j\|_p+\|X_k\|_p-\|X_j+X_k\|_p\big)
--   -\Big(\sum_j\|X_j\|_p-\|X_0+X_1+X_2\|_p\Big)
--   $$
--
--   is convex. Together with the localization lemma, convexity lets an orbit average rule out a negative deficit inside the box.
--
--   **Formalization Note.** Convexity is `ConvexOn ℝ` applied to `tripleDeficit p K` on the same entry box as `local_failure70`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — convexity of the triple deficit on the cutoff-70 asymmetric entry box.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.convex_box70 : ∀ p K : ℝ, 70 ≤ p → (23 / 50 : ℝ) * p ≤ K → K ≤ p →
    ConvexOn ℝ {X : Triple | ∀ j i,
      if j = i then -(219 / 200 : ℝ) ≤ X j i ∧ X j i ≤ -(5217 / 7000 : ℝ)
      else (5217 / 7000 : ℝ) ≤ X j i ∧ X j i ≤ (219 / 200 : ℝ)}
      (tripleDeficit p K) := by sorry
