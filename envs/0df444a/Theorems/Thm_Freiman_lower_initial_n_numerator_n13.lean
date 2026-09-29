-- Prove2me | Theorems.Thm_Freiman_lower_initial_n_numerator_n13
-- name    : Freiman.lower_initial_n_numerator_n13
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:19:50.480753+00:00
-- url     : https://prove2.me/theorems/36018602-7f51-4297-9217-8c370c83c6a9
-- title:
--   Freiman lower construction: initial n numerator n13
-- statement:
--   Exact source quartic numerator obtained from the four displayed pre-period/suffix matrix fractions.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_n_numerator_n13 (x : ℝ) : lowerInitialNNumerator .n13 x = lowerInitialNPolyEval .n13 x := by
  sorry
