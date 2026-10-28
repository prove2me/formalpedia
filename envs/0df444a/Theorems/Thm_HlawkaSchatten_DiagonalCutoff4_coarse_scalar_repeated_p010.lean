-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_repeated_p010
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p010
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:21:44.393585+00:00
-- url     : https://prove2.me/theorems/c184860e-ab69-444a-9c3f-f170d2344fe6
-- title:
--   Hlawka scalar localization budgets above exponent 21/4
-- statement:
--   For every real p≥21/4, the scalar envelope at q=27683/50000 is strictly less than (16357/43750)p, and the maximal-coordinate factor d=81117/100000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_repeated_p010 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) :
    scalarEnvelope p (27683/50000 : ℝ) < (16357/43750 : ℝ)*p ∧ (81117/100000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
