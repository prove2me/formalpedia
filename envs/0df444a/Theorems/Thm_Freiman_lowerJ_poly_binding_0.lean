-- Prove2me | Theorems.Thm_Freiman_lowerJ_poly_binding_0
-- name    : Freiman.lowerJ_poly_binding_0
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:01:06.40571+00:00
-- url     : https://prove2.me/theorems/2a8c73ee-984d-4c46-8f9d-a4b2818a727c
-- title:
--   Freiman repeated-three proof: poly binding 0
-- statement:
--   Exact continued-fraction field identity and positive-denominator cross multiplication for source polynomial 0.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_poly_binding_0 (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) : 0 < lowerJPolyDifference 0 r s ↔ lowerJHStar r s < lowerJH1 r s := by
  sorry
