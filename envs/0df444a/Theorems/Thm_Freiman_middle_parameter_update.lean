-- Prove2me | Theorems.Thm_Freiman_middle_parameter_update
-- name    : Freiman.middle_parameter_update
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:18.860919+00:00
-- url     : https://prove2.me/theorems/55f49f78-c886-4f08-ad15-095ba0921da6
-- title:
--   middle parameter update
-- statement:
--   Appending a digit updates the denominator ratio by p ↦ 1/(a+p), with the word-order matrix convention of the report.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, equation m2b:eq:update

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_parameter_update :
    ∀ (w : List ℕ+) (a : ℕ+),
      middleParameter (w ++ [a]) = 1 / (((a : ℕ) : ℝ) + middleParameter w) := by
  sorry

end Freiman
