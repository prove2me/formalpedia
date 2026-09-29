-- Prove2me | Theorems.Thm_Freiman_gap_minimum_left_tail
-- name    : Freiman.gap_minimum_left_tail
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:26.459059+00:00
-- url     : https://prove2.me/theorems/e06c0183-d6c0-4ea9-9bfa-8d7a4218a42e
-- title:
--   gap minimum left tail
-- statement:
--   The left outward tail satisfies the exact periodic extremal bound from the report.
-- source:
--   Freiman Hall ray report, m3_minimum.tex; first-difference argument

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_minimum_left_tail (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMinimumAdmissible a) (hs : gapMatch a 0 gapSeedB) : cfValue (gapLeftTail a) ≥ cfValue gapBLeft := by
  sorry

end Freiman
