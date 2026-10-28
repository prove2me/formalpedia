-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p003
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p003
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:17:30.991529+00:00
-- url     : https://prove2.me/theorems/a812f3a6-a014-4410-afd7-dcb4d51c0cfc
-- title:
--   Hlawka scalar localization budgets above exponent 131/32
-- statement:
--   For every real p≥131/32, the scalar envelope at q=30463/50000 is strictly less than (30084/81875)p, and the maximal-coordinate factor d=76461/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p003 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) :
    scalarEnvelope p (30463/50000 : ℝ) < (30084/81875 : ℝ)*p ∧ (76461/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
