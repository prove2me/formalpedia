-- Prove2me | Theorems.Thm_Freiman_lower_suffix_target_row1
-- name    : Freiman.lower_suffix_target_row1
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:29.865985+00:00
-- url     : https://prove2.me/theorems/13d01933-f505-4940-b548-559d78fb9754
-- title:
--   Freiman lower construction: suffix target row1
-- statement:
--   History row 1: only the selected covers through current depth, exact source cuts, both target priorities, and marked initial-entry conditions are available. Certificate must include full bounded-history coverage and applicability.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, lem:global-suffix-targets, row 1

import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_suffix_target_row1 (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    ¬ lowerMixed (h n) → ¬ lowerA (h n) 3 → ¬ lowerA (h n) 9 → lowerLStar (h n) → lowerLocalLower (h n) ([2],[1]) ≤ lowerLocalCoordinate (h n) t := by
  sorry
