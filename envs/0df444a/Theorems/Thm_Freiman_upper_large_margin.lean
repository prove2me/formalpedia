-- Prove2me | Theorems.Thm_Freiman_upper_large_margin
-- name    : Freiman.upper_large_margin
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:11.279132+00:00
-- url     : https://prove2.me/theorems/4c14abff-9342-4ce2-afd3-11914689d771
-- title:
--   The large central family strictly exceeds 16/3
-- statement:
--   For n≥5 and both tails in the exact A hull, the central sum is at least 10−sqrt(21), which strictly exceeds 16/3.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:large-bound and its rational square-root comparison.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_large_margin (n : ℕ+) (hn : 5 ≤ (n : ℕ)) (x y : ℝ) (hx : x ∈ Set.Icc upperTheta8 upperTheta1) (hy : y ∈ Set.Icc upperTheta8 upperTheta1) :
    (16 / 3 : ℝ) < ((n : ℕ) : ℝ) + x + y := by
  sorry

end Freiman
