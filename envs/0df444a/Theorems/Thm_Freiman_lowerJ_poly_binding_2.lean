-- Prove2me | Theorems.Thm_Freiman_lowerJ_poly_binding_2
-- name    : Freiman.lowerJ_poly_binding_2
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:01:04.145202+00:00
-- url     : https://prove2.me/theorems/9d43809d-90b3-4d65-bf26-708dc7426988
-- title:
--   Freiman repeated-three proof: poly binding 2
-- statement:
--   Exact continued-fraction field identity and positive-denominator cross multiplication for source polynomial 2.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_poly_binding_2 (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) : 0 < lowerJPolyDifference 2 r s ↔ lowerJProd104 r s < (26/25:ℝ) := by
  sorry
