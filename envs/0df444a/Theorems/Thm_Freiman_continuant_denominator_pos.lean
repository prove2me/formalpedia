-- Prove2me | Theorems.Thm_Freiman_continuant_denominator_pos
-- name    : Freiman.continuant_denominator_pos
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:47.732336+00:00
-- url     : https://prove2.me/theorems/85f2b4b6-fd47-4843-b665-216b3cc538b3
-- title:
--   Positive continuant denominator
-- statement:
--   Every finite positive digit word, including the empty word, has positive current denominator.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.1, found:continuants

import Definitions.Def_Freiman_continuants

namespace Freiman

theorem continuant_denominator_pos (w : List ℕ+) :
    0 < wordContinuantQ w := by
  sorry

end Freiman
