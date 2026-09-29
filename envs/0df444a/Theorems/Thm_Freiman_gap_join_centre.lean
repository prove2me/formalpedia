-- Prove2me | Theorems.Thm_Freiman_gap_join_centre
-- name    : Freiman.gap_join_centre
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:59.770889+00:00
-- url     : https://prove2.me/theorems/242cb758-4aab-4f26-92c0-d1bb731f9bd0
-- title:
--   gap join centre
-- statement:
--   The explicit two-sided join has the prescribed outward tails and central digit four.
-- source:
--   Freiman Hall ray report, m3_maximum.tex and m3_minimum.tex; explicit extremizers

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_join_centre (l r : ℕ → ℕ+) : localValue (gapJoin l r) 0 = 4 + cfValue l + cfValue r := by
  sorry

end Freiman
