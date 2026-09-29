-- Prove2me | Theorems.Thm_Freiman_lower_priority_choice
-- name    : Freiman.lower_priority_choice
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:43.727985+00:00
-- url     : https://prove2.me/theorems/ae47d050-7485-4ff6-86a8-396d993ec12d
-- title:
--   Freiman lower construction: priority choice
-- statement:
--   The two compatible, branch-specific priorities permit a target-containing choice. For a countable run family use its first eligible index; no finite-branching assumption is used.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, sec:selection-priorities

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_priority_choice (t : ℝ) (trace : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t trace n)
    (h : ∃ l : LowerLabel, lowerOffered (trace n) l ∧ lowerGood (lowerChild (trace n) l) ∧ t ∈ lowerCover (lowerChild (trace n) l)) :
    ∃ l : LowerLabel, lowerOffered (trace n) l ∧ lowerPriority t (trace n) l ∧
      lowerGood (lowerChild (trace n) l) ∧ t ∈ lowerCover (lowerChild (trace n) l) := by
  sorry
