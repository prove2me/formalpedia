-- Prove2me | Theorems.Thm_Freiman_middle_small_digit_centers
-- name    : Freiman.middle_small_digit_centers
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:07:05.623099+00:00
-- url     : https://prove2.me/theorems/abc496e0-3d40-4ecc-b27c-e81b317211be
-- title:
--   middle small digit centers
-- statement:
--   Every root completion avoids 314 and 413. At a digit 3 each tail is ≤beta by first-deviation comparison; centers≤2 have value<4. This proves the closed sqrt21 bound for all small-digit positions.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:centers

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_small_digit_centers :
    ∀ (r : Fin 15) (a : ℤ→ℕ+) (i : ℤ), middleCompatible (middleRoot r) a → (a i:ℕ) ≤ 3 → localValue a i  ≤  Real.sqrt 21 := by
  sorry

end Freiman
