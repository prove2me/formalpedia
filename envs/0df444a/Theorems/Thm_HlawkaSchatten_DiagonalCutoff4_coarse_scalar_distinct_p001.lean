-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p001
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p001
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:17:33.288821+00:00
-- url     : https://prove2.me/theorems/dfa064e6-3fb9-4d8b-a6e1-9fd82d29eda2
-- title:
--   Hlawka scalar localization budgets above exponent 129/32
-- statement:
--   For every real p≥129/32, the scalar envelope at q=30797/50000 is strictly less than (49308/134375)p, and the maximal-coordinate factor d=4759/6250 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p001 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) :
    scalarEnvelope p (30797/50000 : ℝ) < (49308/134375 : ℝ)*p ∧ (4759/6250 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
