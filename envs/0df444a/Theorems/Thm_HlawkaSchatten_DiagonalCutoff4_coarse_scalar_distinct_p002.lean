-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p002
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p002
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:17:30.475702+00:00
-- url     : https://prove2.me/theorems/f20ce4ae-4a9f-44d3-98fa-165ba760fb97
-- title:
--   Hlawka scalar localization budgets above exponent 65/16
-- statement:
--   For every real p≥65/16, the scalar envelope at q=12251/20000 is strictly less than (14917/40625)p, and the maximal-coordinate factor d=4769/6250 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p002 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) :
    scalarEnvelope p (12251/20000 : ℝ) < (14917/40625 : ℝ)*p ∧ (4769/6250 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
