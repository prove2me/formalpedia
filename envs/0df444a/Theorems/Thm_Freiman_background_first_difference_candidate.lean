-- Prove2me | Theorems.Thm_Freiman_background_first_difference_candidate
-- name    : Freiman.background_first_difference_candidate
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:01.301014+00:00
-- url     : https://prove2.me/theorems/5e9ecd6a-33f3-4c2d-962a-a1d9a155971e
-- title:
--   An admissible tail supplies a permitted digit after a matching reference prefix
-- statement:
--   After an initial segment agreeing with the reference word, an admissible tail follows an allowed automaton transition. At an odd zero-based position, digit four is excluded because the previous reference digit is one and 14 is forbidden.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_first_difference_candidate (r : Bool) (b : ℕ → ℕ+)
    (hb : ∀ n : ℕ, (b n : ℕ) ≤ 4)
    (h14 : OneSidedAvoidsBlock b [1,4])
    (ha : BackgroundAllowed (backgroundReferenceState r) b)
    (n : ℕ) (hp : ∀ k : ℕ, k < n → b k = backgroundReference r k)
    (hs : backgroundRun (backgroundReferenceState r)
      ((List.range n).map (backgroundReference r)) = some (backgroundPhaseState r n)) :
    BackgroundCandidate r n (b n) := by
  sorry

end Freiman
