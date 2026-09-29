-- Prove2me | Theorems.Thm_Freiman_gap_maximum_left_initial
-- name    : Freiman.gap_maximum_left_initial
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:22.226478+00:00
-- url     : https://prove2.me/theorems/db61dc2f-623d-484c-82eb-2b57f0712144
-- title:
--   gap maximum left initial
-- statement:
--   The fixed seed and the finite initial greedy rows give every allowed left digit comparison before the repeating suffix state.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; greedy left table

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_maximum_left_initial (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMaximumAdmissible a) (hs : gapMatch a 0 gapSeedA) (n : ℕ) (hn : n < 14) (hp : gapSameBefore (gapLeftTail a) gapALeft n) : gapUpperDigit (gapLeftTail a) gapALeft n := by
  sorry

end Freiman
