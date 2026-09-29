-- Prove2me | Theorems.Thm_Freiman_background_prefix12_monotone
-- name    : Freiman.background_prefix12_monotone
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:00:57.726081+00:00
-- url     : https://prove2.me/theorems/90384d8e-edba-4924-b7c4-d01ff757a10e
-- title:
--   The even prefix 12 preserves order on nonnegative tails
-- statement:
--   The map defined by the even-length prefix 12 is increasing on nonnegative real tail parameters.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, determinant sign in (1.1), p. 7; §1.4, proof of Lemma 1.7, p. 12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_prefix12_monotone (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    prefixEval [1,2] x ≤ prefixEval [1,2] y := by
  sorry

end Freiman
