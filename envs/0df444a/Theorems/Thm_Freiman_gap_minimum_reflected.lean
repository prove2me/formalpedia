-- Prove2me | Theorems.Thm_Freiman_gap_minimum_reflected
-- name    : Freiman.gap_minimum_reflected
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:38.495811+00:00
-- url     : https://prove2.me/theorems/caeafbe8-02e6-4024-a961-bc639653c653
-- title:
--   gap minimum reflected
-- statement:
--   The same exact extremal bound holds for the source seed and its reflection.
-- source:
--   Freiman Hall ray report, m3.tex; thm:m3:gap

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_minimum_reflected (a : ℤ → ℕ+) (hc : gapCapped a) (hs : gapMatch a 0 gapSeedB ∨ gapMatch a 0 (gapReverse gapSeedB)) : localValue a 0 ≥ cF := by
  sorry

end Freiman
