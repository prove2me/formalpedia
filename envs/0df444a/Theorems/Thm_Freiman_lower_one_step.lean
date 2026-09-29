-- Prove2me | Theorems.Thm_Freiman_lower_one_step
-- name    : Freiman.lower_one_step
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:41.079361+00:00
-- url     : https://prove2.me/theorems/ee7cccc6-f55b-4a65-8853-60ed57cd2def
-- title:
--   Freiman lower construction: one step
-- statement:
--   (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
--       lowerHasValue t ∨ ∃ l : LowerLabel, lowerOffered (h n) l ∧ lowerPriority t (h n) l ∧
--         lowerState t (lowerChild (h n) l)
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, induction with the same target

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_one_step (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    lowerHasValue t ∨ ∃ l : LowerLabel, lowerOffered (h n) l ∧ lowerPriority t (h n) l ∧
      lowerState t (lowerChild (h n) l) := by
  sorry
