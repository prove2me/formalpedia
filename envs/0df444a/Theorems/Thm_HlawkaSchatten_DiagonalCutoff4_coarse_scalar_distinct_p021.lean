-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p021
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p021
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:20:10.411167+00:00
-- url     : https://prove2.me/theorems/579454f3-838c-4d79-b5bb-ed215e3226c1
-- title:
--   Hlawka scalar localization budgets above exponent 81/16
-- statement:
--   For every real p≥81/16, the scalar envelope at q=56183/100000 is strictly less than (3488/9375)p, and the maximal-coordinate factor d=80491/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p021 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) :
    scalarEnvelope p (56183/100000 : ℝ) < (3488/9375 : ℝ)*p ∧ (80491/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
