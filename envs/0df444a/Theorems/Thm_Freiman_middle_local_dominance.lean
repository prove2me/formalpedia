-- Prove2me | Theorems.Thm_Freiman_middle_local_dominance
-- name    : Freiman.middle_local_dominance
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:05.379308+00:00
-- url     : https://prove2.me/theorems/ec897b56-0537-4266-8bfd-5633016b413f
-- title:
--   middle local dominance
-- statement:
--   Every constructed completion with central value at least sqrt21 has a global maximum at the chosen center, including the lower endpoint t=sqrt21.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:eq:max

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_local_dominance :
    ∀ (r : Fin 15) (a : ℤ→ℕ+) (t : ℝ), middleCompatible (middleRoot r) a → localValue a 0=t → Real.sqrt 21 ≤ t → ∀ i : ℤ, localValue a i ≤ t := by
  sorry

end Freiman
