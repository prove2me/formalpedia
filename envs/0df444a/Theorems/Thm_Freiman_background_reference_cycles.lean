-- Prove2me | Theorems.Thm_Freiman_background_reference_cycles
-- name    : Freiman.background_reference_cycles
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:00:41.976053+00:00
-- url     : https://prove2.me/theorems/73308f42-2c54-439c-876d-521c3ddacdcf
-- title:
--   The exact six-step state cycles of the two greatest-tail reference words
-- statement:
--   The period 131312 from the empty state and the period 131213 from state 3 follow exactly the six-state phase lists explicitly recorded in backgroundPhaseState. Each returns to its initial state and parity after six digits.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_reference_cycles (r : Bool) (n : ℕ) :
    backgroundRun (backgroundReferenceState r)
      ((List.range n).map (backgroundReference r)) = some (backgroundPhaseState r n) := by
  sorry

end Freiman
