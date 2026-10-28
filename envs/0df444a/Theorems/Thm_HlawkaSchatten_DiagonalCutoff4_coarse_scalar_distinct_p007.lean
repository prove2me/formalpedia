-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p007
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p007
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:17:59.658744+00:00
-- url     : https://prove2.me/theorems/a05add8c-2576-4290-b370-b930110ed581
-- title:
--   Hlawka scalar localization budgets above exponent 135/32
-- statement:
--   For every real p≥135/32, the scalar envelope at q=30853/50000 is strictly less than (153448/421875)p, and the maximal-coordinate factor d=4817/6250 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p007 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) :
    scalarEnvelope p (30853/50000 : ℝ) < (153448/421875 : ℝ)*p ∧ (4817/6250 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
