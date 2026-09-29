-- Prove2me | Theorems.Thm_Freiman_gap_periodic_fixed_point
-- name    : Freiman.gap_periodic_fixed_point
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:48.13207+00:00
-- url     : https://prove2.me/theorems/22ab95d7-2e99-4d4a-9087-a7cf88d39a82
-- title:
--   gap periodic fixed point
-- statement:
--   The positive periodic continued fraction is a fixed point of its period map, with the indexing convention checked.
-- source:
--   Freiman Hall ray report, m3_maximum.tex and m3_minimum.tex; periodic-tail evaluation

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_periodic_fixed_point (v : List ℕ+) (hv : v ≠ []) : cfValue (gapEventuallyPeriodic [] v) = prefixEval v (cfValue (gapEventuallyPeriodic [] v)) := by
  sorry

end Freiman
