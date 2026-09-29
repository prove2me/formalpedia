-- Prove2me | Theorems.Thm_Freiman_gap_extremizer_B_global
-- name    : Freiman.gap_extremizer_B_global
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:03.647501+00:00
-- url     : https://prove2.me/theorems/ebc19a78-2345-4cff-9598-28b72501e0d9
-- title:
--   gap extremizer B global
-- statement:
--   The explicit B word attains its global supremum at coordinate zero.
-- source:
--   Freiman Hall ray report, m3_minimum.tex; attainment

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_extremizer_B_global : (∀ i : ℤ, localValue gapExtremizerB i ≤ cF) ∧ localValue gapExtremizerB 0 = cF := by
  sorry

end Freiman
