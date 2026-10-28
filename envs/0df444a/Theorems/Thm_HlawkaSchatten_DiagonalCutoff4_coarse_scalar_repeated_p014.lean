-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p014
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p014
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:22:13.189805+00:00
-- url     : https://prove2.me/theorems/68cf61b9-a001-412e-a5ca-c57b08521048
-- title:
--   Hlawka scalar localization budgets above exponent 23/4
-- statement:
--   For every real p≥23/4, the scalar envelope at q=26803/50000 is strictly less than (217663/575000)p, and the maximal-coordinate factor d=82607/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p014 (p : ℝ) (hpa : (23/4 : ℝ) ≤ p) :
    scalarEnvelope p (26803/50000 : ℝ) < (217663/575000 : ℝ)*p ∧ (82607/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
