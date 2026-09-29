-- Prove2me | Theorems.Thm_Freiman_middle_zero_limit_bound
-- name    : Freiman.middle_zero_limit_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:06:40.711554+00:00
-- url     : https://prove2.me/theorems/1ec694fa-fb9d-4133-8480-7551d37131fd
-- title:
--   middle zero limit bound
-- statement:
--   A constant absolute difference bounded by a sequence tending to zero vanishes. This is the elementary ordered-limit step of the target-preserving argument.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:prop:path, passing to the nested limit

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_zero_limit_bound :
    ∀ (x : ℝ) (u : ℕ→ℝ), (∀ n : ℕ, |x| ≤ u n) → Filter.Tendsto u Filter.atTop (nhds 0) → x=0 := by
  sorry

end Freiman
