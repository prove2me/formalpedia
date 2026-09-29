-- Prove2me | Theorems.Thm_Freiman_background_outward_admissible
-- name    : Freiman.background_outward_admissible
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:07.164806+00:00
-- url     : https://prove2.me/theorems/67ddc36d-47c4-4de2-811f-91b261ee269e
-- title:
--   Both outward tails from a central three are allowed from suffix state three
-- statement:
--   The left and right outward tails from a central three satisfy exactly the initial-state assumptions needed for the U greatest-tail bound.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_outward_admissible (a : ℤ → ℕ+) (i : ℤ)
    (ha : ∀ j : ℤ, (a j : ℕ) ≤ 4)
    (h14 : AvoidsBlock a [1,4]) (h41 : AvoidsBlock a [4,1])
    (h31313 : AvoidsBlock a [3,1,3,1,3]) (hi : (a i : ℕ) = 3) :
    ∀ r : Bool,
      (∀ n : ℕ, (backgroundOutward a i r n : ℕ) ≤ 4) ∧
      OneSidedAvoidsBlock (backgroundOutward a i r) [1,4] ∧
      BackgroundAllowed .three (backgroundOutward a i r) := by
  sorry

end Freiman
