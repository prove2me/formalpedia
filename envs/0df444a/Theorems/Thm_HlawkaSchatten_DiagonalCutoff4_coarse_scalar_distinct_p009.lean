-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p009
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p009
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:18:29.732252+00:00
-- url     : https://prove2.me/theorems/d266baf5-fea9-473e-900c-365b32bab99f
-- title:
--   Hlawka scalar localization budgets above exponent 69/16
-- statement:
--   For every real p≥69/16, the scalar envelope at q=30441/50000 is strictly less than (157247/431250)p, and the maximal-coordinate factor d=77509/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p009 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) :
    scalarEnvelope p (30441/50000 : ℝ) < (157247/431250 : ℝ)*p ∧ (77509/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
