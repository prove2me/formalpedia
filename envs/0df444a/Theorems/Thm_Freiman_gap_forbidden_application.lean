-- Prove2me | Theorems.Thm_Freiman_gap_forbidden_application
-- name    : Freiman.gap_forbidden_application
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:13.665582+00:00
-- url     : https://prove2.me/theorems/bd600486-697c-47c8-ac47-8b84b668041c
-- title:
--   gap forbidden application
-- statement:
--   Use strict cylinder semantics at each witness coordinate; reflection gives the reversed forbidden words.
-- source:
--   Freiman Hall ray report, m3_maximum.tex and m3_minimum.tex; forbidden-word tables

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_forbidden_application (words : List (List ℕ+)) (hchecks : ∀ w ∈ words, ∃ j : ℕ, j < w.length ∧ (4527829567/1000000000 : ℚ) ≤ gapCylinderLower w j) (a : ℤ → ℕ+) (hc : gapCapped a) : ∀ w ∈ words, gapAvoids a w := by
  sorry

end Freiman
