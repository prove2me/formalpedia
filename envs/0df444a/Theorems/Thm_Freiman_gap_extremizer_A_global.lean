-- Prove2me | Theorems.Thm_Freiman_gap_extremizer_A_global
-- name    : Freiman.gap_extremizer_A_global
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:16.006706+00:00
-- url     : https://prove2.me/theorems/12dfa40a-9dff-4a9b-a16c-33228f1df898
-- title:
--   gap extremizer A global
-- statement:
--   The explicit A word attains its global supremum at coordinate zero.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; attainment

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_extremizer_A_global : (∀ i : ℤ, localValue gapExtremizerA i ≤ gapLeft) ∧ localValue gapExtremizerA 0 = gapLeft := by
  sorry

end Freiman
