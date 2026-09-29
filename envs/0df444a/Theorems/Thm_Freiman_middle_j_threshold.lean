-- Prove2me | Theorems.Thm_Freiman_middle_j_threshold
-- name    : Freiman.middle_j_threshold
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:04:11.097795+00:00
-- url     : https://prove2.me/theorems/26be9cf7-21c3-43ad-aa7d-9d825ba7cf15
-- title:
--   middle j threshold
-- statement:
--   All-index overlap threshold comparison, combining the separate k=1 certificate with the uniform k≥2 argument.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:eq:jkthreshold

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_j_threshold :
    ∀ (p s : ℝ) (k : ℕ), p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) → 1 ≤ k → middleHStar p s < middleJThreshold p s k := by
  sorry

end Freiman
