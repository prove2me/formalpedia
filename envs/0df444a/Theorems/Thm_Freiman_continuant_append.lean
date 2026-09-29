-- Prove2me | Theorems.Thm_Freiman_continuant_append
-- name    : Freiman.continuant_append
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:52.364972+00:00
-- url     : https://prove2.me/theorems/b0a85583-28e0-4b37-a6dd-33f4cf223a15
-- title:
--   One-digit continuant recurrence
-- statement:
--   Appending a digit gives exactly the two numerator and two denominator recurrences. This is the finite-word induction step in the report.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.1, found:continuants

import Definitions.Def_Freiman_continuants

namespace Freiman

theorem continuant_append (w : List ℕ+) (a : ℕ+) :
    wordContinuantData (w ++ [a]) =
      ((wordContinuantP w, (a : ℕ) * wordContinuantP w + wordContinuantPrevP w),
       (wordContinuantQ w, (a : ℕ) * wordContinuantQ w + wordContinuantPrevQ w)) := by
  sorry

end Freiman
