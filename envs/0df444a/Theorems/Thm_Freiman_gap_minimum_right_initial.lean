-- Prove2me | Theorems.Thm_Freiman_gap_minimum_right_initial
-- name    : Freiman.gap_minimum_right_initial
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:40.027595+00:00
-- url     : https://prove2.me/theorems/386f33f9-14bc-40ab-b7f2-8008f3c8109c
-- title:
--   gap minimum right initial
-- statement:
--   The fixed seed and the finite initial greedy rows give every allowed right digit comparison before the repeating suffix state.
-- source:
--   Freiman Hall ray report, m3_minimum.tex; greedy right table

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_minimum_right_initial (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMinimumAdmissible a) (hs : gapMatch a 0 gapSeedB) (n : ℕ) (hn : n < 4) (hp : gapSameBefore (gapRightTail a) gapBRight n) : gapLowerDigit (gapRightTail a) gapBRight n := by
  sorry

end Freiman
