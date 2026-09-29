-- Prove2me | Theorems.Thm_Freiman_lowerJ_poly_binding_1
-- name    : Freiman.lowerJ_poly_binding_1
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:01:01.264246+00:00
-- url     : https://prove2.me/theorems/668a7e82-b8d8-4ca1-b470-bce9c6e8406d
-- title:
--   Freiman repeated-three proof: poly binding 1
-- statement:
--   Exact continued-fraction field identity and positive-denominator cross multiplication for source polynomial 1.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_poly_binding_1 (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) : 0 < lowerJPolyDifference 1 r s ↔ lowerJHStar r s < lowerJHBar r s := by
  sorry
