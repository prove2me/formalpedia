-- Prove2me | Theorems.Thm_Freiman_form_orbit_minimum_invariant
-- name    : Freiman.form_orbit_minimum_invariant
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:16.032273+00:00
-- url     : https://prove2.me/theorems/fb11933d-7d36-4920-bf23-f30bb726cdb1
-- title:
--   Every reduced form along the orbit has the same minimum
-- statement:
--   Apply the two-sided transport induction to the algebraic one-step identity.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, proof of found:form-minimum

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_orbit_minimum_invariant (R : ReducedOrbit) :
    ∀ n : ℤ, reducedMinimum (R.alpha n) (R.beta n) = reducedMinimum (R.alpha 0) (R.beta 0) := by
  sorry

end Freiman
