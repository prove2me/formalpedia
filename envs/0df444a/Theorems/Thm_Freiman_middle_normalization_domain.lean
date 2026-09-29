-- Prove2me | Theorems.Thm_Freiman_middle_normalization_domain
-- name    : Freiman.middle_normalization_domain
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:31.168219+00:00
-- url     : https://prove2.me/theorems/605b0826-6ea5-4f7c-abd7-c95ab8beb1dd
-- title:
--   middle normalization domain
-- statement:
--   Normalization preserves both parameter-domain hypotheses and positivity and makes the left width the larger, retaining the original order in a tie.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, cover convention and parameter rectangle

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_normalization_domain :
    ∀ c : MiddleCore, middleRegular c →
      middleRegular (middleNormalized c) ∧
      middleWidth (middleNormalized c).right  ≤  middleWidth (middleNormalized c).left := by
  sorry

end Freiman
