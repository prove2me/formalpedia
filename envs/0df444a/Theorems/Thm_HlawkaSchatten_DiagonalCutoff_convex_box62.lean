-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_convex_box62
-- name    : HlawkaSchatten.DiagonalCutoff.convex_box62
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T07:38:34.859405+00:00
-- url     : https://prove2.me/theorems/e769808d-25b4-45f9-8ebf-b525da8bcc15
-- title:
--   Convexity of the triple deficit on the cutoff-62 entry box
-- statement:
--   For an exponent $p\ge 62$ and a height $K$ between $\frac{23}{50}p$ and $p$, the triple deficit is convex on the cutoff-$62$ asymmetric box.
--
--   On the set of $3\times 3$ real matrices whose diagonal entries lie in $[-\frac{10929}{10000},-\frac{28719}{38750}]$ and whose off-diagonal entries lie in $[\frac{28719}{38750},\frac{10929}{10000}]$, the map sending a matrix to its triple deficit at height $K$ is convex. The Hessian comparison uses a coefficient budget of $7$.
--
--   **Formalization Note.** Convexity is `ConvexOn \mathbb{R}` applied to `tripleDeficit p K` on the same entry box as `local_failure62`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — convexity of the triple deficit on the cutoff-62 asymmetric entry box.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.convex_box62 : ∀ p K : ℝ, 62 ≤ p → (23 / 50 : ℝ) * p ≤ K → K ≤ p →
    ConvexOn ℝ {X : Triple | ∀ j i,
      if j = i then -(10929 / 10000 : ℝ) ≤ X j i ∧ X j i ≤ -(28719 / 38750 : ℝ)
      else (28719 / 38750 : ℝ) ≤ X j i ∧ X j i ≤ (10929 / 10000 : ℝ)}
      (tripleDeficit p K) := by sorry
