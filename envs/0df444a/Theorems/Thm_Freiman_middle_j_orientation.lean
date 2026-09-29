-- Prove2me | Theorems.Thm_Freiman_middle_j_orientation
-- name    : Freiman.middle_j_orientation
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:04:05.152136+00:00
-- url     : https://prove2.me/theorems/e1bb349f-9691-4849-91c3-14ef659d877a
-- title:
--   middle j orientation
-- statement:
--   Every essential J descendant retains the originally wider physical side, strictly, for all k≥1. This is the orientation prerequisite explicitly used before the report’s X_k/Y_(k+2) endpoint subtraction.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:lem:jgood and the paragraph before m2b:eq:jkthreshold

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_j_orientation :
    ∀ (c : MiddleCore) (r : MiddleRow) (k : ℕ), middleRegular c → middleRowCondition c r → middleEssentialJ r = true → 1 ≤ k → 1 < middleWidth ((middleNormalized c).left ++ List.replicate k 3) / middleWidth ((middleNormalized c).right ++ List.replicate k 3) := by
  sorry

end Freiman
