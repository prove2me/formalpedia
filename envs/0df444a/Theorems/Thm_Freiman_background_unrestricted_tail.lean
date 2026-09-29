-- Prove2me | Theorems.Thm_Freiman_background_unrestricted_tail
-- name    : Freiman.background_unrestricted_tail
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:00:39.5552+00:00
-- url     : https://prove2.me/theorems/aaaf20a5-a73a-4a5e-83f1-062c25f9d061
-- title:
--   Every tail on digits one through three is bounded by the period 13
-- statement:
--   Every infinite positive continued-fraction tail with digits at most three is at most [0;overline(1,3)].
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_unrestricted_tail (b : ℕ → ℕ+) (hb : ∀ n : ℕ, (b n : ℕ) ≤ 3) :
    cfValue b ≤ (Real.sqrt 21 - 3) / 2 := by
  sorry

end Freiman
