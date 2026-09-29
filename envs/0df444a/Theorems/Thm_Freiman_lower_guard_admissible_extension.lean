-- Prove2me | Theorems.Thm_Freiman_lower_guard_admissible_extension
-- name    : Freiman.lower_guard_admissible_extension
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:43.289351+00:00
-- url     : https://prove2.me/theorems/7c5bd407-5e41-448f-981f-4c2a75b5584d
-- title:
--   Freiman word guards: admissible extension
-- statement:
--   Compose the existing core extension with the new digits at most three, preserving the checked central word. Normalization uses the already symmetric core list.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerWordGuardData

open Freiman

theorem Freiman.lower_guard_admissible_extension (p : LowerPair) (hp : lowerAdmissible p) (l : LowerLabel) (he : lowerGuardExtensionData p l) : lowerAdmissible (lowerChild p l) := by
  sorry
