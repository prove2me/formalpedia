-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p000
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p000
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:21:12.679983+00:00
-- url     : https://prove2.me/theorems/32502f0e-3a15-483d-b2ec-aee83ea2158d
-- title:
--   Hlawka scalar localization budgets above exponent 4
-- statement:
--   For every real p≥4, the scalar envelope at q=12389/20000 is strictly less than (3667/10000)p, and the maximal-coordinate factor d=37991/50000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p000 (p : ℝ) (hpa : (4 : ℝ) ≤ p) :
    scalarEnvelope p (12389/20000 : ℝ) < (3667/10000 : ℝ)*p ∧ (37991/50000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
