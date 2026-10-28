-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p025
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p025
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:20:45.099167+00:00
-- url     : https://prove2.me/theorems/a63ad057-cda4-4118-9e4c-1745ac332edb
-- title:
--   Hlawka scalar localization budgets above exponent 85/16
-- statement:
--   For every real p≥85/16, the scalar envelope at q=11023/20000 is strictly less than (198939/531250)p, and the maximal-coordinate factor d=81317/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p025 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) :
    scalarEnvelope p (11023/20000 : ℝ) < (198939/531250 : ℝ)*p ∧ (81317/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
