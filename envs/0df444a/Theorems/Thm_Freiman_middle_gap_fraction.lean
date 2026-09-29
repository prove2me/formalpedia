-- Prove2me | Theorems.Thm_Freiman_middle_gap_fraction
-- name    : Freiman.middle_gap_fraction
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:46.62208+00:00
-- url     : https://prove2.me/theorems/ae4b799c-0a9d-4472-9264-b1b298f520a5
-- title:
--   middle gap fraction
-- statement:
--   The separating gap between wider-side branches 2 and 1 exceeds one fifth of the full width, uniformly for real p in [1/4,4/5]. The radical calculation is the one in the report.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:lem:good5

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_gap_fraction :
    ∀ p : ℝ, p ∈ Set.Icc (1/4:ℝ) (4/5) → (1/5:ℝ) < middleGapFraction p := by
  sorry

end Freiman
