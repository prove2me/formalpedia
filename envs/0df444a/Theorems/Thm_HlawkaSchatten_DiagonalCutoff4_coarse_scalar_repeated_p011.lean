-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p011
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p011
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:21:46.420751+00:00
-- url     : https://prove2.me/theorems/df3d8dd6-8faf-41aa-90b0-865c6928c87d
-- title:
--   Hlawka scalar localization budgets above exponent 43/8
-- statement:
--   For every real p≥43/8, the scalar envelope at q=27437/50000 is strictly less than (2016/5375)p, and the maximal-coordinate factor d=81513/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p011 (p : ℝ) (hpa : (43/8 : ℝ) ≤ p) :
    scalarEnvelope p (27437/50000 : ℝ) < (2016/5375 : ℝ)*p ∧ (81513/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
