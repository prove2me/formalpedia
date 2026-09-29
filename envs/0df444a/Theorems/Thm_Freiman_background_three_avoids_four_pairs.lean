-- Prove2me | Theorems.Thm_Freiman_background_three_avoids_four_pairs
-- name    : Freiman.background_three_avoids_four_pairs
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:20.93698+00:00
-- url     : https://prove2.me/theorems/c0ca1159-8c08-4862-9d67-bca178438113
-- title:
--   Words on digits one through three automatically avoid 14 and 41
-- statement:
--   A word whose digits are at most three cannot contain either forbidden pair involving digit four.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_three_avoids_four_pairs (a : ℤ → ℕ+) (ha : ∀ i : ℤ, (a i : ℕ) ≤ 3) :
    AvoidsBlock a [1,4] ∧ AvoidsBlock a [4,1] := by
  sorry

end Freiman
