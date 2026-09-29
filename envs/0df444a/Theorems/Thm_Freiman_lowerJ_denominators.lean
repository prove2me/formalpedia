-- Prove2me | Theorems.Thm_Freiman_lowerJ_denominators
-- name    : Freiman.lowerJ_denominators
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:01:01.99961+00:00
-- url     : https://prove2.me/theorems/7c56747b-e851-4edb-a7ec-f1fff38a2f6c
-- title:
--   Freiman repeated-three proof: denominators
-- statement:
--   Finite positive tail/denominator checks for exactly the four stored threshold pairs.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_denominators (i : Fin 4) (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) : 0 < certThresholdDen (lowerJPolyHigher i) r ∧ 0 < certThresholdDen (lowerJPolyLower i) r := by
  sorry
