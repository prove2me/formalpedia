-- Prove2me | Theorems.Thm_Freiman_lower_initial_period_factor_positive
-- name    : Freiman.lower_initial_period_factor_positive
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:32.731372+00:00
-- url     : https://prove2.me/theorems/b56a99d8-208c-4e4c-aca0-62f2aeece78f
-- title:
--   Freiman lower construction: initial period factor positive
-- statement:
--   Positivity before the smaller root, with the source strict spectral-ratio bound.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_period_factor_positive (x : ℝ) (hx : 0 ≤ x) (hb : x < 43-2*Real.sqrt 462) : 0 < x^2-86*x+1 := by
  sorry
