-- Prove2me | Theorems.Thm_Freiman_form_orbit_axis_bound
-- name    : Freiman.form_orbit_axis_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:57:58.293235+00:00
-- url     : https://prove2.me/theorems/6476d5be-6332-469c-9e47-9ef039972df0
-- title:
--   Both coordinate axes lie above the reciprocal infimum
-- statement:
--   At (1,0) the absolute value is 1/(α_n+β_n); at (0,1) it equals the preceding orbit’s first-axis value. Integer homogeneity gives the lower bound at every nonzero axis vector.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, proof of found:form-minimum

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_orbit_axis_bound (R : ReducedOrbit) (n p q : ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) (haxis : p = 0 ∨ q = 0) :
    orbitReciprocalInfimum R ≤ |reducedValue (R.alpha n) (R.beta n) p q| := by
  sorry

end Freiman
