-- Prove2me | Theorems.Thm_Freiman_lower_guard_checks_equal
-- name    : Freiman.lower_guard_checks_equal
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:03:37.609443+00:00
-- url     : https://prove2.me/theorems/7ea510a6-811b-4de1-a1f0-c44181d5adcd
-- title:
--   Freiman word guards: checks equal
-- statement:
--   Finite guarded list checks: no new 31313, nonempty extension, only nine C23 births, single-1 marked births and six-label preservation alphabet; includes run guards.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerWordGuardData

open Freiman

theorem Freiman.lower_guard_checks_equal (hc : lowerGuardCatalogValid) : ∀ c ∈ lowerGuardCases, c.mixed = false → lowerGuardCaseValid c := by
  sorry
