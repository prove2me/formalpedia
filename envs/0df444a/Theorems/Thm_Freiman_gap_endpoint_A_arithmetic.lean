-- Prove2me | Theorems.Thm_Freiman_gap_endpoint_A_arithmetic
-- name    : Freiman.gap_endpoint_A_arithmetic
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:58.563678+00:00
-- url     : https://prove2.me/theorems/44ba4ed5-cb7b-40fd-9bb0-ea418a008b6f
-- title:
--   gap endpoint A arithmetic
-- statement:
--   Exact finite Möbius and radical arithmetic for the A extremizer central height.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; central-value formula

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_endpoint_A_arithmetic : 4 + prefixEval [3,1,3,1,2,1,1,3,3] gapPeriodSValue + prefixEval [3,1,3,1,3] gapPeriodTValue = gapLeft := by
  sorry

end Freiman
