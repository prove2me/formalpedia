-- Prove2me | Theorems.Thm_Freiman_lower_guard_boundary
-- name    : Freiman.lower_guard_boundary
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:39.100981+00:00
-- url     : https://prove2.me/theorems/710fcff3-0879-4a15-9f6a-bda5d4803597
-- title:
--   Freiman word guards: boundary
-- statement:
--   Only the last proper prefixes of 31313 matter at a new word boundary; the six source suffix classes supply this finite context.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerWordGuardData

open Freiman

theorem Freiman.lower_guard_boundary : LowerGuardBoundaryLaw := by
  sorry
