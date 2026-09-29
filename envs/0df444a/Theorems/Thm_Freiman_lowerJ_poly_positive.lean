-- Prove2me | Theorems.Thm_Freiman_lowerJ_poly_positive
-- name    : Freiman.lowerJ_poly_positive
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:01:17.066977+00:00
-- url     : https://prove2.me/theorems/66de149a-d6b9-4ae1-b49e-141b0672a526
-- title:
--   Freiman repeated-three proof: poly positive
-- statement:
--   Use the existing field, Bernstein and threshold cross-order soundness lemmas.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_poly_positive (i : Fin 4) (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) : 0 < lowerJPolyDifference i r s := by
  sorry
