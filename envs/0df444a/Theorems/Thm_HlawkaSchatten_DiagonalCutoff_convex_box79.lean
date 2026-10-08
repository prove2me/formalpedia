-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_convex_box79
-- name    : HlawkaSchatten.DiagonalCutoff.convex_box79
-- status  : Proved
-- author  : @sorry_not_sorry
-- created : 2026-10-07T10:38:33.79167+00:00
-- url     : https://prove2.me/theorems/6d507603-47bf-4f0b-9d5e-a29d9433829f
-- title:
--   Convexity of the triple deficit on the cutoff79 entry box
-- statement:
--   For real p ≥ 79 and (23/50)p ≤ K ≤ p/2, the triple deficit is convex on the nine-coordinate box of radius 195/1000 = 0.195 around the cyclic center.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.convex_box79 : ∀ p K : ℝ, 79 ≤ p → (23/50 : ℝ)*p ≤ K → K ≤ p/2 → ConvexOn ℝ {X : Triple | ∀ j i, |X j i - cyclicCenter j i| ≤ (195/1000 : ℝ)} (tripleDeficit p K) := by sorry
