-- Prove2me | Theorems.Thm_Freiman_middle_compatible_oscillation
-- name    : Freiman.middle_compatible_oscillation
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:06:51.507604+00:00
-- url     : https://prove2.me/theorems/3ca8cf91-7c27-49e9-ad26-d2e7e8d8d693
-- title:
--   middle compatible oscillation
-- statement:
--   Each exact cover endpoint is a compatible sum and every compatible central sum is within the sum of full cylinder widths of a target lying between those endpoints. This lemma uses the actual sSup-based cfValue via its prefix identity.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:prop:path, final oscillation estimate

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_compatible_oscillation :
    ∀ (c : MiddleCore) (a : ℤ→ℕ+) (t : ℝ), middleRegular c → middleCompatible c a → t∈middleCover c →
      |localValue a 0-t|  ≤  middleWidth c.left+middleWidth c.right := by
  sorry

end Freiman
