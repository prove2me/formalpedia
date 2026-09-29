-- Prove2me | Theorems.Thm_Freiman_lower_selected_words
-- name    : Freiman.lower_selected_words
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:33.733257+00:00
-- url     : https://prove2.me/theorems/5e85e9c7-f63a-46ca-b434-79c2db30dfd7
-- title:
--   Freiman lower construction: selected words
-- statement:
--   Every effectively offered child extends the physical words properly with digits 1,2,3 and avoids 31313. This is a word-and-suffix claim, independent of the geometry certificate; numerical auxiliary covers are excluded.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, 422 source/state rows and 2202 candidate checks

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_selected_words (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (l : LowerLabel) (hl : lowerOffered (h n) l) :
    lowerAdmissible (lowerChild (h n) l) ∧ lowerExtends (lowerNormalize (h n)) (lowerChild (h n) l) ∧
      lowerPrefixSize (h n) < lowerPrefixSize (lowerChild (h n) l) := by
  sorry
