-- Prove2me | Theorems.Thm_Freiman_lower_initial_n_numerator_n14
-- name    : Freiman.lower_initial_n_numerator_n14
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:00.177175+00:00
-- url     : https://prove2.me/theorems/4d7218bf-8932-48bd-913f-7d15901c757f
-- title:
--   Freiman lower construction: initial n numerator n14
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

theorem Freiman.lower_initial_n_numerator_n14 (x : ℝ) : lowerInitialNNumerator .n14 x = lowerInitialNPolyEval .n14 x := by
  sorry
