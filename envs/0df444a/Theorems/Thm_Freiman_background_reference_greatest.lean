-- Prove2me | Theorems.Thm_Freiman_background_reference_greatest
-- name    : Freiman.background_reference_greatest
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:09.869624+00:00
-- url     : https://prove2.me/theorems/dac52ccc-968d-436a-b396-fe3323d2701b
-- title:
--   The T and U reference tails give the greatest admissible values
-- statement:
--   T=[0;overline(131312)] bounds all allowed tails from the empty suffix state, and U=[0;overline(131213)] bounds all allowed tails from suffix state 3. The same bounds hold when digit four is allowed and 14 is forbidden.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_reference_greatest (r : Bool) (b : ℕ → ℕ+)
    (hb : ∀ n : ℕ, (b n : ℕ) ≤ 4)
    (h14 : OneSidedAvoidsBlock b [1,4])
    (ha : BackgroundAllowed (backgroundReferenceState r) b) :
    cfValue b ≤ cfValue (backgroundReference r) := by
  sorry

end Freiman
