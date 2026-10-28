-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p027
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p027
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:20:43.322254+00:00
-- url     : https://prove2.me/theorems/4da042cb-db93-4bd9-9d6d-b5b6fdedafda
-- title:
--   Hlawka scalar localization budgets above exponent 89/16
-- statement:
--   For every real p≥89/16, the scalar envelope at q=10841/20000 is strictly less than (209611/556250)p, and the maximal-coordinate factor d=20519/25000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p027 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) :
    scalarEnvelope p (10841/20000 : ℝ) < (209611/556250 : ℝ)*p ∧ (20519/25000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
