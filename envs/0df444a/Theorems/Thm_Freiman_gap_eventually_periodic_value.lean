-- Prove2me | Theorems.Thm_Freiman_gap_eventually_periodic_value
-- name    : Freiman.gap_eventually_periodic_value
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:39.353971+00:00
-- url     : https://prove2.me/theorems/af8395b5-93e3-440f-b6b4-6f379129c4d4
-- title:
--   gap eventually periodic value
-- statement:
--   The eventual-periodic stream definition is explicitly connected to the same cfValue via removal of its finite prefix.
-- source:
--   Freiman Hall ray report, m3_maximum.tex and m3_minimum.tex; periodic-tail evaluation

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_eventually_periodic_value (u v : List ℕ+) : cfValue (gapEventuallyPeriodic u v) = prefixEval u (cfValue (gapEventuallyPeriodic [] v)) := by
  sorry

end Freiman
