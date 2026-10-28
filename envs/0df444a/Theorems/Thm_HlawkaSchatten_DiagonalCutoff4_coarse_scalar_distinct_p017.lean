-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p017
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p017
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:19:42.501018+00:00
-- url     : https://prove2.me/theorems/3d0006f3-97e6-41f4-a2e7-9a34f70d1c3c
-- title:
--   Hlawka scalar localization budgets above exponent 77/16
-- statement:
--   For every real p≥77/16, the scalar envelope at q=11491/20000 is strictly less than (88931/240625)p, and the maximal-coordinate factor d=19897/25000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p017 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) :
    scalarEnvelope p (11491/20000 : ℝ) < (88931/240625 : ℝ)*p ∧ (19897/25000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
