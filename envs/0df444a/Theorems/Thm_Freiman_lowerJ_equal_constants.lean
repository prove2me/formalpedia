-- Prove2me | Theorems.Thm_Freiman_lowerJ_equal_constants
-- name    : Freiman.lowerJ_equal_constants
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:22.127559+00:00
-- url     : https://prove2.me/theorems/4d6cbdfd-b73d-4da8-8535-568eff6e78de
-- title:
--   Freiman repeated-three proof: equal constants
-- statement:
--   The two exact source coefficient enclosures, four positive differences, five tail order comparisons and two printed rational products.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_equal_constants : (lowerTheta 66-lowerTheta 63)/(lowerTheta 90-lowerTheta 3) < (253/1000:ℝ) ∧ (7/5:ℝ)*(lowerTheta 68-lowerTheta 65)/(lowerTheta 28-lowerTheta 1) < (269/1000:ℝ) ∧ lowerTheta 3 < lowerTheta 30 ∧ lowerTheta 30 < lowerTheta 63 ∧ lowerTheta 63 < lowerTheta 66 ∧ lowerTheta 66 < lowerTheta 90 ∧ lowerTheta 65 < lowerTheta 68 ∧ lowerTheta 1 < lowerTheta 28 ∧ (19/5:ℝ)*(253/1000)*(26/25)<1 ∧ (269/1000:ℝ)<(253/1000)*(133/125) := by
  sorry
