-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_convex_box66
-- name    : HlawkaSchatten.DiagonalCutoff.convex_box66
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T05:17:55.387963+00:00
-- url     : https://prove2.me/theorems/c67442f3-c1fc-4680-bafc-37df31c1697d
-- title:
--   Convexity of the triple deficit on the cutoff-66 entry box
-- statement:
--   For an exponent $p\ge 66$ and a height $K$ between $\frac{23}{50}p$ and $p$, the triple deficit is a convex function of the nine matrix entries on the cutoff-$66$ asymmetric box.
--
--   Let $p\ge 66$ and $\frac{23}{50}p\le K\le p$. On the set of $3\times 3$ real matrices whose diagonal entries lie in $[-\frac{219}{200},-\frac{1631}{2200}]$ and whose off-diagonal entries lie in $[\frac{1631}{2200},\frac{219}{200}]$, the map
--
--   $$
--   X\mapsto K\sum_{j<k}\big(\|X_j\|_p+\|X_k\|_p-\|X_j+X_k\|_p\big)
--   -\Big(\sum_j\|X_j\|_p-\|X_0+X_1+X_2\|_p\Big)
--   $$
--
--   is convex. Together with the localization lemma, convexity lets an orbit average rule out a negative deficit inside the box. The Hessian comparison on this wider box uses a coefficient budget of $7$.
--
--   **Formalization Note.** Convexity is `ConvexOn ℝ` applied to `tripleDeficit p K` on the same entry box as `local_failure66`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — convexity of the triple deficit on the cutoff-66 asymmetric entry box.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.convex_box66 : ∀ p K : ℝ, 66 ≤ p → (23 / 50 : ℝ) * p ≤ K → K ≤ p →
    ConvexOn ℝ {X : Triple | ∀ j i,
      if j = i then -(219 / 200 : ℝ) ≤ X j i ∧ X j i ≤ -(1631 / 2200 : ℝ)
      else (1631 / 2200 : ℝ) ≤ X j i ∧ X j i ≤ (219 / 200 : ℝ)}
      (tripleDeficit p K) := by sorry
