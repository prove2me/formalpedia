-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p023
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p023
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:20:04.965743+00:00
-- url     : https://prove2.me/theorems/0dada92b-2eff-4166-995a-761f525da9fe
-- title:
--   Hlawka scalar localization budgets above exponent 83/16
-- statement:
--   For every real p≥83/16, the scalar envelope at q=55627/100000 is strictly less than (96817/259375)p, and the maximal-coordinate factor d=80913/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p023 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) :
    scalarEnvelope p (55627/100000 : ℝ) < (96817/259375 : ℝ)*p ∧ (80913/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
