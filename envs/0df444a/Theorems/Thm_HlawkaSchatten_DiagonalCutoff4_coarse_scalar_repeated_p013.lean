-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p013
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p013
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:22:21.690041+00:00
-- url     : https://prove2.me/theorems/f25babb1-f286-40a1-bf2e-e0874050e014
-- title:
--   Hlawka scalar localization budgets above exponent 45/8
-- statement:
--   For every real p≥45/8, the scalar envelope at q=26999/50000 is strictly less than (212291/562500)p, and the maximal-coordinate factor d=82257/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p013 (p : ℝ) (hpa : (45/8 : ℝ) ≤ p) :
    scalarEnvelope p (26999/50000 : ℝ) < (212291/562500 : ℝ)*p ∧ (82257/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
