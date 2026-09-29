-- Prove2me | Theorems.Thm_Freiman_gap_seed_centre
-- name    : Freiman.gap_seed_centre
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:38.805073+00:00
-- url     : https://prove2.me/theorems/85ce12b5-7abd-4fa1-8814-3ecab59aa0d9
-- title:
--   gap seed centre
-- statement:
--   Both marked seeds have central digit4, with exactly the stated left/right outward indexing.
-- source:
--   Freiman Hall ray report, m3_maximum.tex and m3_minimum.tex; marked words

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_seed_centre (a : ℤ → ℕ+) (hs : gapMatch a 0 gapSeedA ∨ gapMatch a 0 gapSeedB) : localValue a 0 = 4 + cfValue (gapLeftTail a) + cfValue (gapRightTail a) := by
  sorry

end Freiman
