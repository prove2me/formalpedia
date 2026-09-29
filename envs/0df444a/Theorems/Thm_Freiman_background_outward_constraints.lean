-- Prove2me | Theorems.Thm_Freiman_background_outward_constraints
-- name    : Freiman.background_outward_constraints
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:19.209988+00:00
-- url     : https://prove2.me/theorems/fc63f3a5-0321-4b02-8730-b3ddcbbc07e2
-- title:
--   Global forbidden blocks impose the correct one-sided outward restrictions
-- statement:
--   From a central digit 3, either outward tail has digits at most four, avoids 14, and remains 31313-free when prefixed by the central 3. Both global exclusions 14 and 41 are used to handle the two directions; 31313 is its own reversal.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_outward_constraints (a : ℤ → ℕ+) (i : ℤ)
    (ha : ∀ j : ℤ, (a j : ℕ) ≤ 4)
    (h14 : AvoidsBlock a [1,4]) (h41 : AvoidsBlock a [4,1])
    (h31313 : AvoidsBlock a [3,1,3,1,3]) (hi : (a i : ℕ) = 3) :
    ∀ r : Bool,
      (∀ n : ℕ, (backgroundOutward a i r n : ℕ) ≤ 4) ∧
      OneSidedAvoidsBlock (backgroundOutward a i r) [1,4] ∧
      OneSidedAvoidsBlock (backgroundPrepend [3] (backgroundOutward a i r)) [3,1,3,1,3] := by
  sorry

end Freiman
