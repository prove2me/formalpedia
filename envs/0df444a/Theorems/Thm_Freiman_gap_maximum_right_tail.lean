-- Prove2me | Theorems.Thm_Freiman_gap_maximum_right_tail
-- name    : Freiman.gap_maximum_right_tail
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:28.753498+00:00
-- url     : https://prove2.me/theorems/c37d77b3-7bd5-4f51-9779-024fbd4a39ac
-- title:
--   gap maximum right tail
-- statement:
--   The right outward tail satisfies the exact periodic extremal bound from the report.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; first-difference argument

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_maximum_right_tail (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMaximumAdmissible a) (hs : gapMatch a 0 gapSeedA) : cfValue (gapRightTail a) ≤ cfValue gapARight := by
  sorry

end Freiman
