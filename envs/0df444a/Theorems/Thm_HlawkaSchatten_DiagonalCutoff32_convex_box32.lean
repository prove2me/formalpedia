-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff32_convex_box32
-- name    : HlawkaSchatten.DiagonalCutoff32.convex_box32
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:19:50.033699+00:00
-- url     : https://prove2.me/theorems/68c3c859-6ab9-4935-ad89-1e0b49a3946b
-- title:
--   Convexity of the triple deficit on the cutoff-32 box
-- statement:
--   For real $p\in[32,50]$ and $K\in[0.448\,p,\;p/2]$, the triple deficit
--
--   $$X\mapsto (2K-1)\sum_i\|X_i\|_p+\Big\|\sum_i X_i\Big\|_p-K\sum_{i<j}\|X_i+X_j\|_p$$
--
--   of $3\times 3$ real matrices $X$ with rows $X_0,X_1,X_2$ is convex on the box with diagonal entries in $[-1.065,-0.625]$ and off-diagonal entries in $[0.849,1.121]$.
--
--   Together with orbit averaging this reduces a localized counterexample to a cyclic triple, where the definition of the cyclic constant gives a contradiction.
--
--   **Formalization Note** The deficit is the foundation's `tripleDeficit p K`.
-- source:
--   Sharp diagonal Hlawka constant campaign, cutoff-32 entry (https://prove2.me/campaigns/sharp-diagonal-hlawka-constant); definitions of the foundation mission (Ezzeri Esa, Apache-2.0).

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Mathlib

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff32.convex_box32 : ∀ p K : ℝ, 32 ≤ p → p ≤ 50 →
    (448 / 1000 : ℝ) * p ≤ K → K ≤ p / 2 →
    ConvexOn ℝ {X : Triple | ∀ j i,
      if j = i then -(1065 / 1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625 / 1000 : ℝ)
      else (849 / 1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121 / 1000 : ℝ)}
      (tripleDeficit p K) := by sorry
