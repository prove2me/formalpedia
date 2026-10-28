-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p010
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p010
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:18:26.411985+00:00
-- url     : https://prove2.me/theorems/bc67cfd1-1077-4716-8389-4f716270ad19
-- title:
--   Hlawka scalar localization budgets above exponent 35/8
-- statement:
--   For every real p≥35/8, the scalar envelope at q=6037/10000 is strictly less than (159793/437500)p, and the maximal-coordinate factor d=2431/3125 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p010 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) :
    scalarEnvelope p (6037/10000 : ℝ) < (159793/437500 : ℝ)*p ∧ (2431/3125 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
