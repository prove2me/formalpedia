-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_convex_box63
-- name    : HlawkaSchatten.DiagonalCutoff.convex_box63
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T07:14:54.622183+00:00
-- url     : https://prove2.me/theorems/55405440-b516-4645-a9c2-f8e216e3a55a
-- title:
--   Convexity of the triple deficit on the cutoff-63 entry box
-- statement:
--   For an exponent $p\ge 63$ and a height $K$ between $\frac{23}{50}p$ and $p$, the triple deficit is a convex function of the nine matrix entries on the cutoff-$63$ asymmetric box.
--
--   On the set of $3\times 3$ real matrices whose diagonal entries lie in $[-\frac{273}{250},-\frac{7813}{10500}]$ and whose off-diagonal entries lie in $[\frac{7813}{10500},\frac{273}{250}]$, the map sending a matrix to its triple deficit at height $K$ is convex. The Hessian comparison on this box uses a coefficient budget of $7$.
--
--   **Formalization Note.** Convexity is `ConvexOn \mathbb{R}` applied to `tripleDeficit p K` on the same entry box as `local_failure63`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — convexity of the triple deficit on the cutoff-63 asymmetric entry box.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.convex_box63 : ∀ p K : ℝ, 63 ≤ p → (23 / 50 : ℝ) * p ≤ K → K ≤ p →
    ConvexOn ℝ {X : Triple | ∀ j i,
      if j = i then -(273 / 250 : ℝ) ≤ X j i ∧ X j i ≤ -(7813 / 10500 : ℝ)
      else (7813 / 10500 : ℝ) ≤ X j i ∧ X j i ≤ (273 / 250 : ℝ)}
      (tripleDeficit p K) := by sorry
