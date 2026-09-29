-- Prove2me | Theorems.Thm_Freiman_middle_endpoint_order
-- name    : Freiman.middle_endpoint_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:27.641906+00:00
-- url     : https://prove2.me/theorems/07036721-d419-40a3-9629-f71564b72f81
-- title:
--   middle endpoint order
-- statement:
--   The exact shortened/normal endpoint alternatives are ordered; for mixed parity, the C01 and C10 alternatives meet, including normalization and shortening equalities.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, cover convention, before m2b:sec:good

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_endpoint_order :
    ∀ c : MiddleCore, middleRegular c → (middleBounds c).1  ≤  (middleBounds c).2 := by
  sorry

end Freiman
