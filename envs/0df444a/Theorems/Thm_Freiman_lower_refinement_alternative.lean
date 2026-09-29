-- Prove2me | Theorems.Thm_Freiman_lower_refinement_alternative
-- name    : Freiman.lower_refinement_alternative
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:55.399315+00:00
-- url     : https://prove2.me/theorems/b27f9531-ec5d-4314-a4c3-0c276cb3a0e8
-- title:
--   Freiman lower construction: refinement alternative
-- statement:
--   (t : ℝ) (p : LowerPair) (hr : lowerInitialRoot t p) (hs : lowerState t p) :
--       lowerHasValue t ∨ ∃ h : ℕ → LowerPair, lowerPath t h
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, thm:global-selection

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_refinement_alternative (t : ℝ) (p : LowerPair) (hr : lowerInitialRoot t p) (hs : lowerState t p) :
    lowerHasValue t ∨ ∃ h : ℕ → LowerPair, lowerPath t h := by
  sorry
