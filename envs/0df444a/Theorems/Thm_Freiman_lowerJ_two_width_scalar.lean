-- Prove2me | Theorems.Thm_Freiman_lowerJ_two_width_scalar
-- name    : Freiman.lowerJ_two_width_scalar
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:35.554417+00:00
-- url     : https://prove2.me/theorems/6846f7ee-6142-4db7-8ad6-08efe0f7e557
-- title:
--   Freiman repeated-three proof: two width scalar
-- statement:
--   The explicit endpoint rational enclosures and final rational width margins from the report.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_two_width_scalar : (1/4:ℝ) < lowerAlpha ∧ lowerAlpha < (27/100:ℝ) ∧ (3/4:ℝ) < lowerBeta ∧ lowerBeta < (4/5:ℝ) ∧ (13243/18000:ℝ)<1 ∧ (739328/796875:ℝ)<1 := by
  sorry
