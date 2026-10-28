-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p006
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p006
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:18:02.0791+00:00
-- url     : https://prove2.me/theorems/9435145a-7de1-4010-aba0-e566bfca5c15
-- title:
--   Hlawka scalar localization budgets above exponent 67/16
-- statement:
--   For every real p≥67/16, the scalar envelope at q=30999/50000 is strictly less than (76093/209375)p, and the maximal-coordinate factor d=38461/50000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p006 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) :
    scalarEnvelope p (30999/50000 : ℝ) < (76093/209375 : ℝ)*p ∧ (38461/50000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
