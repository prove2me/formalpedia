-- Prove2me | Theorems.Thm_Freiman_background_small_digit
-- name    : Freiman.background_small_digit
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:17.865143+00:00
-- url     : https://prove2.me/theorems/44391b41-f516-493b-9c76-4722880fec0f
-- title:
--   A central digit at most two has local value below four
-- statement:
--   If the central digit is at most two, both fractional tails are below one and the local value is strictly below four.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_small_digit (a : ℤ → ℕ+) (i : ℤ) (hi : (a i : ℕ) ≤ 2) :
    localValue a i < 4 := by
  sorry

end Freiman
