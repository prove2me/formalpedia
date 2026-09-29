-- Prove2me | Theorems.Thm_Freiman_gap_tail_comparison
-- name    : Freiman.gap_tail_comparison
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:44.860213+00:00
-- url     : https://prove2.me/theorems/26fc30ee-fee8-4a9f-90a5-da045e7608c1
-- title:
--   gap tail comparison
-- statement:
--   Generic maximum/minimum comparison from the strict alternating rule.
-- source:
--   Freiman Hall ray report, m3_maximum.tex and m3_minimum.tex

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_tail_comparison (b c : ℕ → ℕ+) : ((∀ n, gapSameBefore b c n → gapUpperDigit b c n) → cfValue b ≤ cfValue c) ∧ ((∀ n, gapSameBefore b c n → gapLowerDigit b c n) → cfValue c ≤ cfValue b) := by
  sorry

end Freiman
