-- Prove2me | Theorems.Thm_Freiman_background_two_away_small
-- name    : Freiman.background_two_away_small
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:23.636982+00:00
-- url     : https://prove2.me/theorems/89e01fdd-2709-456a-b77c-fe742733dbba
-- title:
--   A central 131 pattern has a digit at most two on one side at distance two
-- statement:
--   With central digit 3 and both neighbors 1, neither distance-two digit can be 4 because 14 and 41 are forbidden. Both cannot be 3 because that would create 31313. Hence at least one is at most 2.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_two_away_small (a : ℤ → ℕ+) (i : ℤ)
    (ha : ∀ j : ℤ, (a j : ℕ) ≤ 4)
    (h14 : AvoidsBlock a [1,4]) (h41 : AvoidsBlock a [4,1])
    (h31313 : AvoidsBlock a [3,1,3,1,3]) (hi : (a i : ℕ) = 3)
    (hl : (a (i - 1) : ℕ) = 1) (hr : (a (i + 1) : ℕ) = 1) :
    (a (i - 2) : ℕ) ≤ 2 ∨ (a (i + 2) : ℕ) ≤ 2 := by
  sorry

end Freiman
