-- Prove2me | Theorems.Thm_Freiman_background_drop_two_constraints
-- name    : Freiman.background_drop_two_constraints
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:03.863194+00:00
-- url     : https://prove2.me/theorems/b57d257a-dac1-4a43-8d2f-ad2dadca1002
-- title:
--   Prefixes 11 and 12 reset the forbidden-word state
-- statement:
--   After the first two digits 11 or 12 are removed from an admissible tail starting after a central 3, the remaining tail starts in the empty suffix state and retains its digit bound and avoidance of 14.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_drop_two_constraints (b : ℕ → ℕ+)
    (hb : ∀ n : ℕ, (b n : ℕ) ≤ 4)
    (h14 : OneSidedAvoidsBlock b [1,4]) (ha : BackgroundAllowed .three b)
    (h0 : (b 0 : ℕ) = 1) (h1 : (b 1 : ℕ) ≤ 2) :
    (∀ n : ℕ, (b (n + 2) : ℕ) ≤ 4) ∧
      OneSidedAvoidsBlock (fun n => b (n + 2)) [1,4] ∧
      BackgroundAllowed .empty (fun n => b (n + 2)) := by
  sorry

end Freiman
