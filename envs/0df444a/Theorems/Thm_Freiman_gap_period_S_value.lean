-- Prove2me | Theorems.Thm_Freiman_gap_period_S_value
-- name    : Freiman.gap_period_S_value
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:44.912713+00:00
-- url     : https://prove2.me/theorems/83bb694a-ed5a-4ed7-a528-37e33d3595d6
-- title:
--   gap period S value
-- statement:
--   The periodic stream [3,1,3,1,2,1] has its stated exact radical value.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; exact tail evaluations

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_period_S_value : cfValue (gapEventuallyPeriodic [] [3,1,3,1,2,1]) = gapPeriodSValue := by
  sorry

end Freiman
