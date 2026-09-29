-- Prove2me | Theorems.Thm_Freiman_gap_minimum_right_tail
-- name    : Freiman.gap_minimum_right_tail
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:30.231287+00:00
-- url     : https://prove2.me/theorems/0d2c2c9b-e9b8-487c-90a9-ad9b722d99e1
-- title:
--   gap minimum right tail
-- statement:
--   The right outward tail satisfies the exact periodic extremal bound from the report.
-- source:
--   Freiman Hall ray report, m3_minimum.tex; first-difference argument

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_minimum_right_tail (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMinimumAdmissible a) (hs : gapMatch a 0 gapSeedB) : cfValue (gapRightTail a) ≥ cfValue gapBRight := by
  sorry

end Freiman
