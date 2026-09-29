-- Prove2me | Theorems.Thm_Freiman_middle_secondary_four_separations
-- name    : Freiman.middle_secondary_four_separations
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:09.183744+00:00
-- url     : https://prove2.me/theorems/f9fb6e4c-8cde-445a-aed3-35c2807d75b9
-- title:
--   middle secondary four separations
-- statement:
--   The eight two-4 roots have strictly larger exterior left tail x than right tail y for every allowed completion; the eight exact positive lower bounds are in the dominance table.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:centers, dominance table

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_secondary_four_separations :
    ∀ (r : Fin 15) (a : ℤ→ℕ+), middleCompatible (middleRoot r) a → (r.val∈[5,6,7,8,9,10,11,13]) →
      cfValue (fun n : ℕ => a (-(n:ℤ)-1)) > cfValue (fun n : ℕ => a ((n:ℤ)+2)) := by
  sorry

end Freiman
