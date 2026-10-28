-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p012
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p012
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:22:16.285538+00:00
-- url     : https://prove2.me/theorems/3cccea4d-fdab-4377-8ded-15c0b62d1616
-- title:
--   Hlawka scalar localization budgets above exponent 11/2
-- statement:
--   For every real p≥11/2, the scalar envelope at q=2721/5000 is strictly less than (25867/68750)p, and the maximal-coordinate factor d=20473/25000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p012 (p : ℝ) (hpa : (11/2 : ℝ) ≤ p) :
    scalarEnvelope p (2721/5000 : ℝ) < (25867/68750 : ℝ)*p ∧ (20473/25000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
