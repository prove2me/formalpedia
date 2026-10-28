-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p030
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p030
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:21:19.292983+00:00
-- url     : https://prove2.me/theorems/abe2a537-6167-4aab-b5b8-eec0a515e8c9
-- title:
--   Hlawka scalar localization budgets above exponent 95/16
-- statement:
--   For every real p≥95/16, the scalar envelope at q=10613/20000 is strictly less than (225753/593750)p, and the maximal-coordinate factor d=41553/50000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p030 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) :
    scalarEnvelope p (10613/20000 : ℝ) < (225753/593750 : ℝ)*p ∧ (41553/50000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
