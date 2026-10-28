-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p008
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p008
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:18:03.893606+00:00
-- url     : https://prove2.me/theorems/6dc2687c-664a-46cf-85b0-51039fcffe21
-- title:
--   Hlawka scalar localization budgets above exponent 17/4
-- statement:
--   For every real p≥17/4, the scalar envelope at q=3839/6250 is strictly less than (154711/425000)p, and the maximal-coordinate factor d=3861/5000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p008 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) :
    scalarEnvelope p (3839/6250 : ℝ) < (154711/425000 : ℝ)*p ∧ (3861/5000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
