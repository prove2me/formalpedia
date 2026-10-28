-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p015
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p015
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:18:53.096004+00:00
-- url     : https://prove2.me/theorems/551158ef-9230-40a0-88be-3a8613c5f5fe
-- title:
--   Hlawka scalar localization budgets above exponent 75/16
-- statement:
--   For every real p≥75/16, the scalar envelope at q=11637/20000 is strictly less than (57553/156250)p, and the maximal-coordinate factor d=15821/20000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p015 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) :
    scalarEnvelope p (11637/20000 : ℝ) < (57553/156250 : ℝ)*p ∧ (15821/20000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
