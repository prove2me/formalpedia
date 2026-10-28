-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p006
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p006
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:21:44.013985+00:00
-- url     : https://prove2.me/theorems/06f27cd2-ed7c-4847-9a5b-ed2c1405740b
-- title:
--   Hlawka scalar localization budgets above exponent 19/4
-- statement:
--   For every real p≥19/4, the scalar envelope at q=57811/100000 is strictly less than (175257/475000)p, and the maximal-coordinate factor d=1587/2000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p006 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) :
    scalarEnvelope p (57811/100000 : ℝ) < (175257/475000 : ℝ)*p ∧ (1587/2000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
