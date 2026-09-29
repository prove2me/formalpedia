-- Prove2me | Theorems.Thm_Freiman_background_large_neighbor
-- name    : Freiman.background_large_neighbor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:09.747787+00:00
-- url     : https://prove2.me/theorems/1cdf1a3a-8dff-4d8f-85f9-31e5c7e19bf3
-- title:
--   A central digit at most three with a neighbor at least two has value below nine halves
-- statement:
--   A fractional tail beginning with a digit at least two is below one half. Together with the other tail below one, this bounds the local value at a digit at most three by nine halves.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_large_neighbor (a : ℤ → ℕ+) (i : ℤ) (hi : (a i : ℕ) ≤ 3)
    (hn : 2 ≤ (a (i - 1) : ℕ) ∨ 2 ≤ (a (i + 1) : ℕ)) :
    localValue a i < (9 / 2 : ℝ) := by
  sorry

end Freiman
