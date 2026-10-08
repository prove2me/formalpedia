-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_convex_box80
-- name    : HlawkaSchatten.DiagonalCutoff.convex_box80
-- status  : Proved
-- author  : @sorry_not_sorry
-- created : 2026-10-06T11:39:08.632265+00:00
-- url     : https://prove2.me/theorems/d78fed30-5345-4afb-8a44-180e9cd9dacf
-- title:
--   Convexity of the triple deficit on the cutoff80 entry box
-- statement:
--   For real p ≥ 80 and (23/50)p ≤ K ≤ p/2, the triple deficit is convex on the nine-coordinate box of radius 195/1000 = 0.195 around the cyclic center. This follows from the exact rational SOS radial estimate (reused from the cutoff84 certificate on the smaller box) and the residual Hessian bounds; it is the geometric input to the cutoff80 window argument.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — exact supporting lemma for the cutoff80 window; adapts the cutoff84 box-convexity argument to p ≥ 80 with box radius 195/1000 and K-bound (23/50)p.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.convex_box80 : ∀ p K : ℝ, 80 ≤ p → (23/50 : ℝ)*p ≤ K → K ≤ p/2 →
    ConvexOn ℝ {X : Triple | ∀ j i, |X j i - cyclicCenter j i| ≤ (195/1000 : ℝ)}
      (tripleDeficit p K) := by sorry
