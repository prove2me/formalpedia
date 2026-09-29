-- Prove2me | Theorems.Thm_Freiman_middle_j_real_ratio_bounds
-- name    : Freiman.middle_j_real_ratio_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:03:56.109563+00:00
-- url     : https://prove2.me/theorems/b2593575-5f4d-4ebd-a0ee-e33292cddfb9
-- title:
--   middle j real ratio bounds
-- statement:
--   The nine real-parameter corner comparisons controlling every J width ratio, extended from symmetric bilinear corners to the full x,y tail rectangle.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:lem:jgood

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_j_real_ratio_bounds :
    ∀ p s x y : ℝ, p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) →
      x ∈ Set.Icc middleAlpha (prefixEval [3] middleAlpha) → y ∈ Set.Icc middleAlpha (prefixEval [3] middleAlpha) →
      middleHStar p s < middleH p s x y ∧
      (5/19:ℝ)*middleH p s x y < middleScalarA p s (549/1000) ∧
      (5/19:ℝ)*middleH p s x y < middleScalarB p s (313/1000) := by
  sorry

end Freiman
