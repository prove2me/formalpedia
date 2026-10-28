-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p015
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p015
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:22:17.055883+00:00
-- url     : https://prove2.me/theorems/ff0c6b82-ca15-4bf5-b271-be528934fcf1
-- title:
--   Hlawka scalar localization budgets above exponent 47/8
-- statement:
--   For every real p≥47/8, the scalar envelope at q=53239/100000 is strictly less than (223053/587500)p, and the maximal-coordinate factor d=82943/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p015 (p : ℝ) (hpa : (47/8 : ℝ) ≤ p) :
    scalarEnvelope p (53239/100000 : ℝ) < (223053/587500 : ℝ)*p ∧ (82943/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
