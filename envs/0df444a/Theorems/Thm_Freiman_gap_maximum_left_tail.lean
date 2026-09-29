-- Prove2me | Theorems.Thm_Freiman_gap_maximum_left_tail
-- name    : Freiman.gap_maximum_left_tail
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:26.224698+00:00
-- url     : https://prove2.me/theorems/7d61f426-f269-4c7b-af8d-5a4afa78d2c4
-- title:
--   gap maximum left tail
-- statement:
--   The left outward tail satisfies the exact periodic extremal bound from the report.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; first-difference argument

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_maximum_left_tail (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMaximumAdmissible a) (hs : gapMatch a 0 gapSeedA) : cfValue (gapLeftTail a) ≤ cfValue gapALeft := by
  sorry

end Freiman
