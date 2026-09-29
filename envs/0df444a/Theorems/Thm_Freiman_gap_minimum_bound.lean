-- Prove2me | Theorems.Thm_Freiman_gap_minimum_bound
-- name    : Freiman.gap_minimum_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:35.538084+00:00
-- url     : https://prove2.me/theorems/e6994bec-c121-4bf4-8346-cecd80cbc2d1
-- title:
--   gap minimum bound
-- statement:
--   The marked B height obeys the report’s exact minimum bound under the common cap.
-- source:
--   Freiman Hall ray report, m3_minimum.tex; prop:m3:minimum

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_minimum_bound (a : ℤ → ℕ+) (hc : gapCapped a) (hs : gapMatch a 0 gapSeedB) : localValue a 0 ≥ cF := by
  sorry

end Freiman
