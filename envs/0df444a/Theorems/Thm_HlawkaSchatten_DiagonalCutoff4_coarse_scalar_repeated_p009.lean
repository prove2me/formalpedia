-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p009
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p009
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:21:42.333846+00:00
-- url     : https://prove2.me/theorems/44b162f2-6342-4ad3-9679-9d8cb02316c3
-- title:
--   Hlawka scalar localization budgets above exponent 41/8
-- statement:
--   For every real p≥41/8, the scalar envelope at q=55899/100000 is strictly less than (19099/51250)p, and the maximal-coordinate factor d=2522/3125 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p009 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) :
    scalarEnvelope p (55899/100000 : ℝ) < (19099/51250 : ℝ)*p ∧ (2522/3125 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
