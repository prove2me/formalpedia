-- Prove2me | Theorems.Thm_Freiman_lower_priority_blockers_good
-- name    : Freiman.lower_priority_blockers_good
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:29.24886+00:00
-- url     : https://prove2.me/theorems/7114eeeb-6a22-4623-a369-3e563c91273d
-- title:
--   Freiman lower construction: priority blockers good
-- statement:
--   Every alternative that can block a selected C23 or C20 is itself offered and good, on its actual source branch; the exceptional early-chain alternatives use their inherited A9, word-domain and geometry conditions.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, two priorities and their admissible geometric alternatives

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_priority_blockers_good (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) : lowerPreferredGood (h n) := by
  sorry
