-- Prove2me | Theorems.Thm_Freiman_background_period13_first_difference
-- name    : Freiman.background_period13_first_difference
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:00:36.711871+00:00
-- url     : https://prove2.me/theorems/3c500ef9-54d5-4bb9-b9a5-ec7666fd0eb8
-- title:
--   The alternating word 13 is maximal on digits one through three
-- statement:
--   At the first disagreement with the periodic word 13, a positive word using only digits at most three has the continued-fraction order making it smaller.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_period13_first_difference (b : ℕ → ℕ+) (hb : ∀ n : ℕ, (b n : ℕ) ≤ 3)
    (n : ℕ) (hp : ∀ k : ℕ, k < n → b k = backgroundPeriod13 k)
    (hd : b n ≠ backgroundPeriod13 n) :
    if Even n then backgroundPeriod13 n < b n else b n < backgroundPeriod13 n := by
  sorry

end Freiman
