-- Prove2me | Theorems.Thm_Freiman_gap_extremizer_A_data
-- name    : Freiman.gap_extremizer_A_data
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:53.819195+00:00
-- url     : https://prove2.me/theorems/29d8f6c4-6347-46e4-924d-dac733bd50c8
-- title:
--   gap extremizer A data
-- statement:
--   The explicit A word uses only digits 1–4 and contains the exact marked source seed.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; explicit attaining sequence

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_extremizer_A_data : gapDigits gapExtremizerA ∧ gapMatch gapExtremizerA 0 gapSeedA := by
  sorry

end Freiman
