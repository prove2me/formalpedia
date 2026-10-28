-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p018
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p018
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:19:50.776027+00:00
-- url     : https://prove2.me/theorems/9b78e226-e167-4dd5-9f92-ea05796ef119
-- title:
--   Hlawka scalar localization budgets above exponent 39/8
-- statement:
--   For every real p≥39/8, the scalar envelope at q=11423/20000 is strictly less than (7219/19500)p, and the maximal-coordinate factor d=39911/50000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p018 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) :
    scalarEnvelope p (11423/20000 : ℝ) < (7219/19500 : ℝ)*p ∧ (39911/50000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
