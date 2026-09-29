-- Prove2me | Theorems.Thm_Freiman_cfValue_le_of_first_difference
-- name    : Freiman.cfValue_le_of_first_difference
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:43.325929+00:00
-- url     : https://prove2.me/theorems/6564ecf1-16f0-452a-805b-1cca86c9b021
-- title:
--   Alternating first-difference comparisons bound two infinite continued fractions
-- statement:
--   If every possible first differing digit has the alternating order which makes b smaller than c, then cfValue b is at most cfValue c. Indices start at zero.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, first sentence of the proof of Lemma 1.7, p. 11, using §1.1, equation (1.1), p. 7.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem cfValue_le_of_first_difference (b c : ℕ → ℕ+)
    (h : ∀ n : ℕ, (∀ k : ℕ, k < n → b k = c k) → b n ≠ c n →
      if Even n then c n < b n else b n < c n) :
    cfValue b ≤ cfValue c := by
  sorry

end Freiman
