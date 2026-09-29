-- Prove2me | Theorems.Thm_Freiman_perronValue_gt_digit
-- name    : Freiman.perronValue_gt_digit
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:36.291368+00:00
-- url     : https://prove2.me/theorems/062c6876-e44b-463b-9f6f-d3456381a276
-- title:
--   Every Perron value strictly exceeds its central digit
-- statement:
--   The finite backward tail is nonnegative and the infinite forward tail is strictly positive.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, lower bound two in found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem perronValue_gt_digit (b : ℕ → ℕ+) (n : ℕ) :
    ((b n:ℕ):ℝ) < perronValue b n := by
  sorry

end Freiman
