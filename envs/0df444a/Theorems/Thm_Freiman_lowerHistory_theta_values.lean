-- Prove2me | Theorems.Thm_Freiman_lowerHistory_theta_values
-- name    : Freiman.lowerHistory_theta_values
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:53.635049+00:00
-- url     : https://prove2.me/theorems/1841b210-6f6a-4c59-86f3-f3ef405eb535
-- title:
--   Freiman.lowerHistory_theta_values
-- statement:
--   The fourteen source threshold tails are the actual lowerTheta entries.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); lower_core.tex, eq:lc-natural-tails and eq:lc-full-width; global_selection.tex, lem:global-suffix-targets; verification/families/target_selection/verify_h5_original_independent.py; role: source threshold table

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_theta_values :
    ∀ i ∈ ([3,20,22,25,28,35,36,63,65,66,68,70,90,94] : List ℕ), certFieldVal (lowerHistoryTheta i) = lowerTheta i := by
  sorry
