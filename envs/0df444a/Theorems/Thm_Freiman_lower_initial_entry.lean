-- Prove2me | Theorems.Thm_Freiman_lower_initial_entry
-- name    : Freiman.lower_initial_entry
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:20.949341+00:00
-- url     : https://prove2.me/theorems/41171a70-33f3-48fe-afa2-ef34775d7c21
-- title:
--   Freiman lower construction: initial entry
-- statement:
--   (t : ℝ) (ht : t ∈ Set.Icc cF (Real.sqrt 21)) :
--       lowerHasValue t ∨ ∃ p : LowerPair, lowerInitialRoot t p ∧ lowerState t p
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, initial induction step

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_initial_entry (t : ℝ) (ht : t ∈ Set.Icc cF (Real.sqrt 21)) :
    lowerHasValue t ∨ ∃ p : LowerPair, lowerInitialRoot t p ∧ lowerState t p := by
  sorry
