-- Prove2me | Theorems.Thm_Freiman_gap_order_comparison
-- name    : Freiman.gap_order_comparison
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:37.136106+00:00
-- url     : https://prove2.me/theorems/fe5dc557-5712-4ba9-9f03-7b99c06664dd
-- title:
--   gap order comparison
-- statement:
--   Choose the least differing index to turn all allowed digit comparisons into the two non-strict tail bounds.
-- source:
--   Freiman Hall ray report, m3_maximum.tex and m3_minimum.tex; first-difference arguments

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_order_comparison (horder : ∀ (b c : ℕ → ℕ+) (n : ℕ), gapSameBefore b c n → b n ≠ c n → (cfValue b < cfValue c ↔ if Even n then c n < b n else b n < c n)) (b c : ℕ → ℕ+) : ((∀ n, gapSameBefore b c n → gapUpperDigit b c n) → cfValue b ≤ cfValue c) ∧ ((∀ n, gapSameBefore b c n → gapLowerDigit b c n) → cfValue c ≤ cfValue b) := by
  sorry

end Freiman
