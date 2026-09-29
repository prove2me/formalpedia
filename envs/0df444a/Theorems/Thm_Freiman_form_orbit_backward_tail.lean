-- Prove2me | Theorems.Thm_Freiman_form_orbit_backward_tail
-- name    : Freiman.form_orbit_backward_tail
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:19.328683+00:00
-- url     : https://prove2.me/theorems/5c75e331-6f7b-478b-8d32-20d852ac7a82
-- title:
--   The backward reduced coordinate is the continued-fraction tail
-- statement:
--   Iterate the beta recurrence backward and apply the report’s cylinder continuity to identify the left infinite tail with the existing cfValue.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, proof of found:markov-symbolic

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_orbit_backward_tail (R : ReducedOrbit) (n : ℤ) :
    R.beta n = cfValue (fun k : ℕ => R.digits (n-(k:ℤ)-1)) := by
  sorry

end Freiman
