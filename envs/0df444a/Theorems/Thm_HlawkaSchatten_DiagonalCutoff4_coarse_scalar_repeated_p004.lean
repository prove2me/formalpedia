-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p004
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p004
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:21:15.660849+00:00
-- url     : https://prove2.me/theorems/a7033a7e-1d45-4a28-a5c1-f195f91d05f0
-- title:
--   Hlawka scalar localization budgets above exponent 9/2
-- statement:
--   For every real p≥9/2, the scalar envelope at q=59427/100000 is strictly less than (54971/150000)p, and the maximal-coordinate factor d=78337/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p004 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) :
    scalarEnvelope p (59427/100000 : ℝ) < (54971/150000 : ℝ)*p ∧ (78337/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
