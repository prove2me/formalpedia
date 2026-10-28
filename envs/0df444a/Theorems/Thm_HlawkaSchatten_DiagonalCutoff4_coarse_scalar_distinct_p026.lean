-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p026
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p026
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:20:43.762003+00:00
-- url     : https://prove2.me/theorems/22fcef44-4fb6-4e43-8c05-045b3fe77892
-- title:
--   Hlawka scalar localization budgets above exponent 87/16
-- statement:
--   For every real p≥87/16, the scalar envelope at q=54643/100000 is strictly less than (40853/108750)p, and the maximal-coordinate factor d=10213/12500 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p026 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) :
    scalarEnvelope p (54643/100000 : ℝ) < (40853/108750 : ℝ)*p ∧ (10213/12500 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
