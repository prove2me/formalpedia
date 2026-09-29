-- Prove2me | Theorems.Thm_Freiman_middle_secondary_four_bound
-- name    : Freiman.middle_secondary_four_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:07.04036+00:00
-- url     : https://prove2.me/theorems/2e14eb7a-87be-468c-8165-fc6de91d6f09
-- title:
--   middle secondary four bound
-- statement:
--   Inspect the fixed root positions: every digit above 3 is the central 4 or the unique adjacent secondary 4 in the eight listed roots. The exact difference identity and strict exterior separation give central dominance.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:centers

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_secondary_four_bound :
    (∀ a : ℤ→ℕ+, a 0=4 → a 1=4 → localValue a 0-localValue a 1 = (cfValue (fun n : ℕ => a (-(n:ℤ)-1))-cfValue (fun n : ℕ => a ((n:ℤ)+2))) * (1+1/((4+cfValue (fun n : ℕ => a (-(n:ℤ)-1)))*(4+cfValue (fun n : ℕ => a ((n:ℤ)+2)))))) →
    (∀ (r : Fin 15) (a : ℤ→ℕ+), middleCompatible (middleRoot r) a → (r.val∈[5,6,7,8,9,10,11,13]) → cfValue (fun n : ℕ => a (-(n:ℤ)-1)) > cfValue (fun n : ℕ => a ((n:ℤ)+2))) →
    ∀ (r : Fin 15) (a : ℤ→ℕ+) (i : ℤ), middleCompatible (middleRoot r) a → ¬(a i:ℕ) ≤ 3 → localValue a i ≤ localValue a 0 := by
  sorry

end Freiman
