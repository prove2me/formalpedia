-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p028
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p028
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:20:47.729589+00:00
-- url     : https://prove2.me/theorems/4712e6c2-3310-41f0-8b6a-839ae6f2d828
-- title:
--   Hlawka scalar localization budgets above exponent 91/16
-- statement:
--   For every real p≥91/16, the scalar envelope at q=26899/50000 is strictly less than (8599/22750)p, and the maximal-coordinate factor d=82433/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p028 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) :
    scalarEnvelope p (26899/50000 : ℝ) < (8599/22750 : ℝ)*p ∧ (82433/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
