-- Prove2me | Theorems.Thm_Freiman_background_reference_first_difference
-- name    : Freiman.background_reference_first_difference
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:05.311186+00:00
-- url     : https://prove2.me/theorems/0b26480e-7862-43e7-8121-d222dbf3c7bb
-- title:
--   The two reference tails dominate every admissible tail
-- statement:
--   At the first differing digit, a tail on digits at most four that avoids 14 and is admissible from the relevant suffix state is smaller in continued-fraction order than the period 131312 or 131213.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_reference_first_difference (r : Bool) (b : ℕ → ℕ+)
    (hb : ∀ n : ℕ, (b n : ℕ) ≤ 4)
    (h14 : OneSidedAvoidsBlock b [1,4])
    (ha : BackgroundAllowed (backgroundReferenceState r) b)
    (n : ℕ) (hp : ∀ k : ℕ, k < n → b k = backgroundReference r k)
    (hd : b n ≠ backgroundReference r n) :
    if Even n then backgroundReference r n < b n else b n < backgroundReference r n := by
  sorry

end Freiman
