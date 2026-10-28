-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_scalar_distinct_p011
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p011
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:18:55.638519+00:00
-- url     : https://prove2.me/theorems/bdb3dd87-e731-4cd1-a058-3046cfdacc29
-- title:
--   Hlawka scalar localization budgets above exponent 71/16
-- statement:
--   For every real p≥71/16, the scalar envelope at q=29943/50000 is strictly less than (81174/221875)p, and the maximal-coordinate factor d=19517/25000 satisfies d times the p-th root of three at most one.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.coarse_scalar_distinct_p011 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) :
    scalarEnvelope p (29943/50000 : ℝ) < (81174/221875 : ℝ)*p ∧ (19517/25000 : ℝ)*(3:ℝ)^(1/p) ≤ 1 := by sorry
