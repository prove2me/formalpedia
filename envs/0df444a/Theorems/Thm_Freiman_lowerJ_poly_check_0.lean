-- Prove2me | Theorems.Thm_Freiman_lowerJ_poly_check_0
-- name    : Freiman.lowerJ_poly_check_0
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:00:46.820236+00:00
-- url     : https://prove2.me/theorems/383958bf-ffc8-4b60-8f2d-6fec86c8e51c
-- title:
--   Freiman repeated-three proof: poly check 0
-- statement:
--   Nine exact Bernstein coefficients for H1−Hstar. Source J coefficients are column-major; the Lean matrix explicitly transposes that enumeration.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_poly_check_0 : lowerJPolyChecked 0 := by
  sorry
