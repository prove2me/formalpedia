-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p013
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p013
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:18:53.897739+00:00
-- url     : https://prove2.me/theorems/95df300b-0945-4c4c-8879-94e45fe9dcac
-- title:
--   Hlawka scalar localization budgets above exponent 73/16
-- statement:
--   For every real p≥73/16, the scalar envelope at q=58991/100000 is strictly less than (167487/456250)p, and the maximal-coordinate factor d=78599/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p013 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) :
    scalarEnvelope p (58991/100000 : ℝ) < (167487/456250 : ℝ)*p ∧ (78599/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
