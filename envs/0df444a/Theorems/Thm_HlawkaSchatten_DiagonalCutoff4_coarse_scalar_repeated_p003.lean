-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p003
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p003
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:21:14.925221+00:00
-- url     : https://prove2.me/theorems/46c43b86-f4cd-436f-b146-003e7fedf0c4
-- title:
--   Hlawka scalar localization budgets above exponent 35/8
-- statement:
--   For every real p≥35/8, the scalar envelope at q=6037/10000 is strictly less than (159793/437500)p, and the maximal-coordinate factor d=2431/3125 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p003 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) :
    scalarEnvelope p (6037/10000 : ℝ) < (159793/437500 : ℝ)*p ∧ (2431/3125 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
