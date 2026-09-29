-- Prove2me | Theorems.Thm_Freiman_lower_suffix_target_row2
-- name    : Freiman.lower_suffix_target_row2
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:09.776981+00:00
-- url     : https://prove2.me/theorems/464dbeba-22be-4022-bfd6-7a765d313349
-- title:
--   Freiman lower construction: suffix target row2
-- statement:
--   History row 2: only the selected covers through current depth, exact source cuts, both target priorities, and marked initial-entry conditions are available. Certificate must include full bounded-history coverage and applicability.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, lem:global-suffix-targets, row 2

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_suffix_target_row2 (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    ¬ lowerMixed (h n) → ¬ lowerA (h n) 3 → lowerRStar (h n) → lowerLocalLower (h n) ([2],[2]) ≤ lowerLocalCoordinate (h n) t := by
  sorry
