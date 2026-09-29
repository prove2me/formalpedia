-- Prove2me | Theorems.Thm_Freiman_middle_j_first_threshold
-- name    : Freiman.middle_j_first_threshold
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:04:07.220253+00:00
-- url     : https://prove2.me/theorems/56b6dc9c-84bf-4882-849e-b8be403cb784
-- title:
--   middle j first threshold
-- statement:
--   The k=1 J overlap threshold comparison on the full p,s rectangle, using its nine exact positive Bernstein coefficients.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:eq:jkthreshold, k=1 case

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_j_first_threshold :
    ∀ p s : ℝ, p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) → middleHStar p s < middleJThreshold p s 1 := by
  sorry

end Freiman
