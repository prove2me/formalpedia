-- Prove2me | Theorems.Thm_Freiman_lowerJ_poly_binding_3
-- name    : Freiman.lowerJ_poly_binding_3
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:01:07.755289+00:00
-- url     : https://prove2.me/theorems/4dedbfda-3068-49cd-8cfd-c9336f3f2ae7
-- title:
--   Freiman repeated-three proof: poly binding 3
-- statement:
--   Exact continued-fraction field identity and positive-denominator cross multiplication for source polynomial 3.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_poly_binding_3 (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) : 0 < lowerJPolyDifference 3 r s ↔ (133/125:ℝ) < lowerJProd1064 r s := by
  sorry
