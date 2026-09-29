-- Prove2me | Theorems.Thm_Freiman_upper_sum_one
-- name    : Freiman.upper_sum_one
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:45.901657+00:00
-- url     : https://prove2.me/theorems/52eefc20-a8cb-411f-b7cc-7c777a840b27
-- title:
--   The restricted self-sum contains its full endpoint interval: one
-- statement:
--   Applying the proved reduction of the normal-deletion theorem to this explicit tree yields the whole required closed self-sum interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:sum-intervals.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_sum_one  :
    Set.Icc (2 * upperTheta2) (2 * upperTheta1) ⊆ upperSumSet upperKOne upperKOne := by
  sorry

end Freiman
