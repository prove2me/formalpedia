-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p005
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p005
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:21:12.746109+00:00
-- url     : https://prove2.me/theorems/2a103f1d-9cfd-4837-a9ef-bcf8a8b2934f
-- title:
--   Hlawka scalar localization budgets above exponent 37/8
-- statement:
--   For every real p≥37/8, the scalar envelope at q=29289/50000 is strictly less than (170069/462500)p, and the maximal-coordinate factor d=15771/20000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p005 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) :
    scalarEnvelope p (29289/50000 : ℝ) < (170069/462500 : ℝ)*p ∧ (15771/20000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
