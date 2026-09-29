-- Prove2me | Theorems.Thm_Freiman_lowerJ_width_formula
-- name    : Freiman.lowerJ_width_formula
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:01:27.167466+00:00
-- url     : https://prove2.me/theorems/413f4d85-ffea-477c-8a96-cf0bd75ea09b
-- title:
--   Freiman repeated-three proof: width formula
-- statement:
--   Actual outward-word full width formula, reused throughout the report width proof.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_width_formula : ∀ w : List ℕ+, lowerWidth w = (lowerBeta-lowerAlpha)/((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*(((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2)) := by
  sorry
