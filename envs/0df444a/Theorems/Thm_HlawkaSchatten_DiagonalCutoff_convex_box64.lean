-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_convex_box64
-- name    : HlawkaSchatten.DiagonalCutoff.convex_box64
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T06:50:27.926718+00:00
-- url     : https://prove2.me/theorems/d6675791-80e8-46ae-ae7b-729cda1e4077
-- title:
--   Convexity of the triple deficit on the cutoff-64 entry box
-- statement:
--   For an exponent $p\ge 64$ and a height $K$ between $\frac{23}{50}p$ and $p$, the triple deficit is a convex function of the nine matrix entries on the cutoff-$64$ asymmetric box.
--
--   Let $p\ge 64$ and $\frac{23}{50}p\le K\le p$. On the set of $3\times 3$ real matrices whose diagonal entries lie in $[-\frac{273}{250},-\frac{23847}{32000}]$ and whose off-diagonal entries lie in $[\frac{23847}{32000},\frac{273}{250}]$, the map sending a matrix to its triple deficit at height $K$ is convex. Together with the localization lemma, convexity lets an orbit average rule out a negative deficit inside the box. The Hessian comparison on this box uses a coefficient budget of $7$.
--
--   **Formalization Note.** Convexity is `ConvexOn \mathbb{R}` applied to `tripleDeficit p K` on the same entry box as `local_failure64`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — convexity of the triple deficit on the cutoff-64 asymmetric entry box.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.convex_box64 : ∀ p K : ℝ, 64 ≤ p → (23 / 50 : ℝ) * p ≤ K → K ≤ p →
    ConvexOn ℝ {X : Triple | ∀ j i,
      if j = i then -(273 / 250 : ℝ) ≤ X j i ∧ X j i ≤ -(23847 / 32000 : ℝ)
      else (23847 / 32000 : ℝ) ≤ X j i ∧ X j i ≤ (273 / 250 : ℝ)}
      (tripleDeficit p K) := by sorry
