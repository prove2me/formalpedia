-- Prove2me | Theorems.Thm_Freiman_lower_guard_offered
-- name    : Freiman.lower_guard_offered
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:33.174001+00:00
-- url     : https://prove2.me/theorems/b411bd87-aff2-44ea-b04c-95f1187a0875
-- title:
--   Freiman word guards: offered
-- statement:
--   Reduce every offered word to an explicit finite source row or a repeated-3 continuation of length at least three.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerWordGuardData

open Freiman

theorem Freiman.lower_guard_offered (p : LowerPair) (hp : lowerAdmissible p) (l : LowerLabel) (hl : lowerOffered p l) : lowerGuardAllowed p l := by
  sorry
