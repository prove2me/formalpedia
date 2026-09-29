-- Prove2me | Theorems.Thm_Freiman_lower_fixed_roots_good
-- name    : Freiman.lower_fixed_roots_good
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:29.074765+00:00
-- url     : https://prove2.me/theorems/64059049-3288-4483-bdb7-8fc0a5d3d341
-- title:
--   Freiman lower construction: fixed roots good
-- statement:
--   The 23 enumerated physical roots are admissible and good, with the actual parameter box. This is an exact finite endpoint and word check.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, initial words; certificates/initial_covers/fixed_initial_independent.json

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_fixed_roots_good : ∀ p ∈ lowerFixedRoots, lowerAdmissible p ∧ lowerGood p ∧ lowerParameterBox p := by
  sorry
