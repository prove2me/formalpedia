-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_convex_box84
-- name    : HlawkaSchatten.DiagonalCutoff.convex_box84
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T05:01:28.26667+00:00
-- url     : https://prove2.me/theorems/cd5a8979-0d0e-472d-8744-ed7125e11b41
-- title:
--   Convexity of the triple deficit on the cutoff84 entry box
-- statement:
--   For real p ≥ 84 and 20p/43 ≤ K ≤ p/2, the triple deficit is convex on the nine-coordinate box of radius 1953/10000 around the cyclic center. This follows from the exact rational SOS radial estimate and the residual Hessian bounds; it is the geometric input to the cutoff84 window argument.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — exact supporting lemma for the locally verified Codex cutoff84 continuation; CUTOFF84-ARGUMENT.md, scalar confinement and coupled box curvature sections.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.convex_box84 : ∀ p K : ℝ, 84 ≤ p → (20/43 : ℝ)*p ≤ K → K ≤ p/2 →
    ConvexOn ℝ {X : Triple | ∀ j i, |X j i - cyclicCenter j i| ≤ (1953/10000 : ℝ)}
      (tripleDeficit p K) := by sorry
