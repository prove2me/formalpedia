-- Prove2me | Theorems.Thm_Freiman_background_short_tail_bound
-- name    : Freiman.background_short_tail_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:13.816552+00:00
-- url     : https://prove2.me/theorems/69fc9fa6-e125-451e-9e23-a2df4453e0a2
-- title:
--   The side beginning with one and then at most two has the sharper bound
-- statement:
--   An admissible tail after a central 3, beginning with 1 and a digit at most 2, is at most T_12(T)=(2 sqrt(462)-29)/19.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_short_tail_bound (b : ℕ → ℕ+)
    (hb : ∀ n : ℕ, (b n : ℕ) ≤ 4)
    (h14 : OneSidedAvoidsBlock b [1,4]) (ha : BackgroundAllowed .three b)
    (h0 : (b 0 : ℕ) = 1) (h1 : (b 1 : ℕ) ≤ 2) :
    cfValue b ≤ (2 * Real.sqrt 462 - 29) / 19 := by
  sorry

end Freiman
