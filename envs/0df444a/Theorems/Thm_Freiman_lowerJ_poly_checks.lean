-- Prove2me | Theorems.Thm_Freiman_lowerJ_poly_checks
-- name    : Freiman.lowerJ_poly_checks
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:00:48.992983+00:00
-- url     : https://prove2.me/theorems/a3867d66-131d-49c0-bea9-17034b0511a2
-- title:
--   Freiman repeated-three proof: poly checks
-- statement:
--   All four concrete polynomial tables.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_poly_checks (i : Fin 4) : lowerJPolyChecked i := by
  sorry
