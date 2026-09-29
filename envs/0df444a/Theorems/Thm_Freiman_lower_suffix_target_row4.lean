-- Prove2me | Theorems.Thm_Freiman_lower_suffix_target_row4
-- name    : Freiman.lower_suffix_target_row4
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:21.488497+00:00
-- url     : https://prove2.me/theorems/a93fe7b1-464c-49aa-9357-0037ffa2b9f9
-- title:
--   Freiman lower construction: suffix target row4
-- statement:
--   History row 4: only the selected covers through current depth, exact source cuts, both target priorities, and marked initial-entry conditions are available. Certificate must include full bounded-history coverage and applicability.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, lem:global-suffix-targets, row 4

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_suffix_target_row4 (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    lowerMixed (h n) → ¬ lowerH (h n) 2 → ¬ lowerH (h n) 5 → ¬ lowerRStar (h n) := by
  sorry
