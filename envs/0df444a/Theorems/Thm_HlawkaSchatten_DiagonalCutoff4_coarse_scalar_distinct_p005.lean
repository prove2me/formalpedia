-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p005
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p005
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:17:30.496459+00:00
-- url     : https://prove2.me/theorems/89764a75-7430-48d1-82be-cf652db36e7c
-- title:
--   Hlawka scalar localization budgets above exponent 133/32
-- statement:
--   For every real p≥133/32, the scalar envelope at q=31149/50000 is strictly less than (150928/415625)p, and the maximal-coordinate factor d=76771/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p005 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) :
    scalarEnvelope p (31149/50000 : ℝ) < (150928/415625 : ℝ)*p ∧ (76771/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
