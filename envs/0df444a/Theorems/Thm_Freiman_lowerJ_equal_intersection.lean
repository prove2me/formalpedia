-- Prove2me | Theorems.Thm_Freiman_lowerJ_equal_intersection
-- name    : Freiman.lowerJ_equal_intersection
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:22.994981+00:00
-- url     : https://prove2.me/theorems/d3d91d11-bb48-40d6-9140-13c6e2a84ebd
-- title:
--   Freiman repeated-three proof: equal intersection
-- statement:
--   The recorded endpoint formulas, source tail order and the strict signed contact give a point in the two defining source fork intervals.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_equal_intersection (hc : (lowerTheta 66-lowerTheta 63)/(lowerTheta 90-lowerTheta 3) < (253/1000:ℝ) ∧ (7/5:ℝ)*(lowerTheta 68-lowerTheta 65)/(lowerTheta 28-lowerTheta 1) < (269/1000:ℝ) ∧ lowerTheta 3 < lowerTheta 30 ∧ lowerTheta 30 < lowerTheta 63 ∧ lowerTheta 63 < lowerTheta 66 ∧ lowerTheta 66 < lowerTheta 90 ∧ lowerTheta 65 < lowerTheta 68 ∧ lowerTheta 1 < lowerTheta 28 ∧ (19/5:ℝ)*(253/1000)*(26/25)<1 ∧ (269/1000:ℝ)<(253/1000)*(133/125)) (p : LowerPair) (ha : lowerAdmissible p) (hp : ¬ lowerMixed p) (hl : lowerEnds p.1 [3]) (hr : lowerEnds p.2 [3]) (hb : lowerParameterBox p) (hwide : lowerWidth p.2 ≤ lowerWidth p.1) (hratio : lowerWidth p.1 < (19/5:ℝ)*lowerWidth p.2) (ht : lowerJEqualContact p) (he : lowerJEqualForkFacts p) : lowerSourceGood p := by
  sorry
