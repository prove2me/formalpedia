-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p020
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p020
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:19:53.522721+00:00
-- url     : https://prove2.me/theorems/944ba987-21fb-4650-a15f-6dcf23616cc1
-- title:
--   Hlawka scalar localization budgets above exponent 5
-- statement:
--   For every real p≥5, the scalar envelope at q=353/625 is strictly less than (4643/12500)p, and the maximal-coordinate factor d=80273/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p020 (p : ℝ) (hpa : (5 : ℝ) ≤ p) :
    scalarEnvelope p (353/625 : ℝ) < (4643/12500 : ℝ)*p ∧ (80273/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
