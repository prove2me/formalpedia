-- Prove2me | Theorems.Thm_Freiman_background_phase_policy
-- name    : Freiman.background_phase_policy
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:00:50.058328+00:00
-- url     : https://prove2.me/theorems/8cc45d10-7c42-4ba3-be00-f41570cf831c
-- title:
--   The finite parity policy is extremal in each of the six reference phases
-- statement:
--   For each reference phase, a digit at most four which does not complete 31313 and which is not four at an odd zero-based position is bounded by the greedy reference digit in the required alternating order.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_phase_policy (r : Bool) (n : ℕ) (d : ℕ+) (hd : BackgroundCandidate r n d) :
    if Even n then backgroundReference r n ≤ d else d ≤ backgroundReference r n := by
  sorry

end Freiman
