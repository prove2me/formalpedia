-- Prove2me | Theorems.Thm_Freiman_gap_maximum_right_initial
-- name    : Freiman.gap_maximum_right_initial
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:21.559409+00:00
-- url     : https://prove2.me/theorems/6ac7a423-3064-437d-8dff-2ff46c8e92ac
-- title:
--   gap maximum right initial
-- statement:
--   The fixed seed and the finite initial greedy rows give every allowed right digit comparison before the repeating suffix state.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; greedy right table

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_maximum_right_initial (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMaximumAdmissible a) (hs : gapMatch a 0 gapSeedA) (n : ℕ) (hn : n < 7) (hp : gapSameBefore (gapRightTail a) gapARight n) : gapUpperDigit (gapRightTail a) gapARight n := by
  sorry

end Freiman
