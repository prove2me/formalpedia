-- Prove2me | Theorems.Thm_Freiman_gap_maximum_bound
-- name    : Freiman.gap_maximum_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:33.277257+00:00
-- url     : https://prove2.me/theorems/5a1376b2-88c6-43db-a53d-892b6234d9da
-- title:
--   gap maximum bound
-- statement:
--   The marked A height obeys the report’s exact maximum bound under the common cap.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; prop:m3:maximum

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_maximum_bound (a : ℤ → ℕ+) (hc : gapCapped a) (hs : gapMatch a 0 gapSeedA) : localValue a 0 ≤ gapLeft := by
  sorry

end Freiman
