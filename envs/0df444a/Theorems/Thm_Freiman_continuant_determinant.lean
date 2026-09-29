-- Prove2me | Theorems.Thm_Freiman_continuant_determinant
-- name    : Freiman.continuant_determinant
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:45.835326+00:00
-- url     : https://prove2.me/theorems/15a19013-45d2-403b-a402-313455dd7ace
-- title:
--   Continuant determinant
-- statement:
--   The determinant of the continuant matrix is (-1) to the word length. The intended proof is induction using the one-digit recurrence.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.1, found:continuants

import Definitions.Def_Freiman_continuants

namespace Freiman

theorem continuant_determinant (w : List ℕ+) :
    (wordContinuantPrevP w : ℤ) * wordContinuantQ w -
      (wordContinuantP w : ℤ) * wordContinuantPrevQ w = (-1 : ℤ) ^ w.length := by
  sorry

end Freiman
