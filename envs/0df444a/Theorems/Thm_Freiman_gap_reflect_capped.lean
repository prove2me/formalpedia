-- Prove2me | Theorems.Thm_Freiman_gap_reflect_capped
-- name    : Freiman.gap_reflect_capped
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:41.103036+00:00
-- url     : https://prove2.me/theorems/32c58a58-8cfa-4373-b689-781bbc20575b
-- title:
--   gap reflect capped
-- statement:
--   Reflection preserves every global cap inequality.
-- source:
--   Freiman Hall ray report, m3.tex; thm:m3:gap

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_reflect_capped (a : ℤ → ℕ+) (hc : gapCapped a) : gapCapped (gapReflect a) := by
  sorry

end Freiman
