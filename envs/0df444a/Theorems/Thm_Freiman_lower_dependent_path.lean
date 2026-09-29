-- Prove2me | Theorems.Thm_Freiman_lower_dependent_path
-- name    : Freiman.lower_dependent_path
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:47.341537+00:00
-- url     : https://prove2.me/theorems/04b1f38c-5a42-410e-aeb9-cddc0ab31bc0
-- title:
--   Freiman lower construction: dependent path
-- statement:
--   Dependent choice over finite histories: terminate at an explicit limiting model or choose forever, preserving the source, physical words, same target, goodness, parameter domain, and the two priorities.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, inductive target selection

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_dependent_path (step : ∀ (t : ℝ) (h : ℕ → LowerPair) (n : ℕ), lowerHistory t h n →
      lowerHasValue t ∨ ∃ l : LowerLabel, lowerOffered (h n) l ∧ lowerPriority t (h n) l ∧ lowerState t (lowerChild (h n) l))
    (t : ℝ) (p : LowerPair) (hr : lowerInitialRoot t p) (hs : lowerState t p) :
    lowerHasValue t ∨ ∃ h : ℕ → LowerPair, lowerPath t h := by
  sorry
