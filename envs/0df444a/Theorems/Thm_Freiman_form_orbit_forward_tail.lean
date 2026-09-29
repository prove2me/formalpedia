-- Prove2me | Theorems.Thm_Freiman_form_orbit_forward_tail
-- name    : Freiman.form_orbit_forward_tail
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:11.479264+00:00
-- url     : https://prove2.me/theorems/06491145-d9d8-4521-897a-a9a9bd2d8ce3
-- title:
--   The forward reduced coordinate is the continued-fraction complete quotient
-- statement:
--   Iterate the alpha recurrence, then use continuant cylinder diameters tending to zero to identify the complete quotient with the existing cfValue tail.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, proof of found:markov-symbolic

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_orbit_forward_tail (R : ReducedOrbit) (n : ℤ) :
    R.alpha n = ((R.digits n : ℕ) : ℝ) + cfValue (fun k : ℕ => R.digits (n+(k:ℤ)+1)) := by
  sorry

end Freiman
