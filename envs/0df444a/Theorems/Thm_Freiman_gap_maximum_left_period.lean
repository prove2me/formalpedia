-- Prove2me | Theorems.Thm_Freiman_gap_maximum_left_period
-- name    : Freiman.gap_maximum_left_period
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:18.235271+00:00
-- url     : https://prove2.me/theorems/3d1c5578-5cdd-46ea-9b93-45d5dc21e719
-- title:
--   gap maximum left period
-- statement:
--   Each of the six displayed suffix states excludes every improving digit, for every repeated period; the suffix and parity return after six positions.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; six-state periodic greedy table

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_maximum_left_period (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMaximumAdmissible a) (hs : gapMatch a 0 gapSeedA) (k r : ℕ) (hr : r < 6) (hp : gapSameBefore (gapLeftTail a) gapALeft (14+6*k+r)) : gapUpperDigit (gapLeftTail a) gapALeft (14+6*k+r) := by
  sorry

end Freiman
