-- Prove2me | Theorems.Thm_Freiman_middle_adjacent_four_identity
-- name    : Freiman.middle_adjacent_four_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:02.295107+00:00
-- url     : https://prove2.me/theorems/ab42e5e1-3134-4683-a034-2b5491d38fda
-- title:
--   middle adjacent four identity
-- statement:
--   Exact adjacent-4 central-value difference, using the existing cfValue first-digit identity on both facing tails.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:centers, displayed λ0−λ1 identity

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_adjacent_four_identity :
    ∀ a : ℤ→ℕ+, a 0=4 → a 1=4 →
      localValue a 0-localValue a 1 =
      (cfValue (fun n : ℕ => a (-(n:ℤ)-1))-cfValue (fun n : ℕ => a ((n:ℤ)+2))) *
      (1+1/((4+cfValue (fun n : ℕ => a (-(n:ℤ)-1)))*(4+cfValue (fun n : ℕ => a ((n:ℤ)+2))))) := by
  sorry

end Freiman
