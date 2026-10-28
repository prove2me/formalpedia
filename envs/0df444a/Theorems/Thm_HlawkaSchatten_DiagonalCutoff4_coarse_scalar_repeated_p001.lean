-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p001
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p001
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:21:13.404512+00:00
-- url     : https://prove2.me/theorems/7ffa89a7-a8ea-4431-a0ab-dbd301e827bb
-- title:
--   Hlawka scalar localization budgets above exponent 33/8
-- statement:
--   For every real p≥33/8, the scalar envelope at q=62607/100000 is strictly less than (37418/103125)p, and the maximal-coordinate factor d=76617/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p001 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) :
    scalarEnvelope p (62607/100000 : ℝ) < (37418/103125 : ℝ)*p ∧ (76617/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
