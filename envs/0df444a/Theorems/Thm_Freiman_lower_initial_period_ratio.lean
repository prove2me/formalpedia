-- Prove2me | Theorems.Thm_Freiman_lower_initial_period_ratio
-- name    : Freiman.lower_initial_period_ratio
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:52.902064+00:00
-- url     : https://prove2.me/theorems/fd71977d-0763-4d3f-aa41-35e4d88b407a
-- title:
--   Freiman lower construction: initial period ratio
-- statement:
--   The actual recurrence ratio x_n lies below the smaller period-matrix eigenvalue root and in the exact source rational box, including x0=0.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_period_ratio (n : ℕ) : 0 ≤ lowerInitialX n ∧ lowerInitialX n < 43-2*Real.sqrt 462 ∧ lowerInitialX n ≤ (1/85:ℝ) := by
  sorry
