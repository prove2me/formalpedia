-- Prove2me | Theorems.Thm_Freiman_gap_maximum_reflected
-- name    : Freiman.gap_maximum_reflected
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:44.506975+00:00
-- url     : https://prove2.me/theorems/b13a47f3-7d3c-4932-bced-94f0e21a5c58
-- title:
--   gap maximum reflected
-- statement:
--   The same exact extremal bound holds for the source seed and its reflection.
-- source:
--   Freiman Hall ray report, m3.tex; thm:m3:gap

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_maximum_reflected (a : ℤ → ℕ+) (hc : gapCapped a) (hs : gapMatch a 0 gapSeedA ∨ gapMatch a 0 (gapReverse gapSeedA)) : localValue a 0 ≤ gapLeft := by
  sorry

end Freiman
