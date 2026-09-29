-- Prove2me | Theorems.Thm_Freiman_gap_period_T_value
-- name    : Freiman.gap_period_T_value
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:47.154546+00:00
-- url     : https://prove2.me/theorems/1b2f0eca-d9ff-42fa-9bcd-4ed2194efb73
-- title:
--   gap period T value
-- statement:
--   The periodic stream [4,4,4,3,2,3] has its stated exact radical value.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; exact tail evaluations

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_period_T_value : cfValue (gapEventuallyPeriodic [] [4,4,4,3,2,3]) = gapPeriodTValue := by
  sorry

end Freiman
