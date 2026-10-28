-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p019
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p019
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:19:48.893247+00:00
-- url     : https://prove2.me/theorems/8722dc89-6fb7-4bdf-a584-57782ef845e2
-- title:
--   Hlawka scalar localization budgets above exponent 79/16
-- statement:
--   For every real p≥79/16, the scalar envelope at q=5679/10000 is strictly less than (91547/246875)p, and the maximal-coordinate factor d=1601/2000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p019 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) :
    scalarEnvelope p (5679/10000 : ℝ) < (91547/246875 : ℝ)*p ∧ (1601/2000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
