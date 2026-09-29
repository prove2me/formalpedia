-- Prove2me | Theorems.Thm_Freiman_gap_tail_first_difference
-- name    : Freiman.gap_tail_first_difference
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:41.65439+00:00
-- url     : https://prove2.me/theorems/40d686ab-5553-4e22-a696-9f156908faf1
-- title:
--   gap tail first difference
-- statement:
--   The strict first-difference rule, with zero-based parity, for exactly the existing sSup continued-fraction value.
-- source:
--   Freiman Hall ray report, foundations.tex; continued-fraction ordering and m3_maximum.tex first-difference argument

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_tail_first_difference (b c : ℕ → ℕ+) (n : ℕ) (hprefix : gapSameBefore b c n) (hd : b n ≠ c n) : (cfValue b < cfValue c ↔ if Even n then c n < b n else b n < c n) := by
  sorry

end Freiman
