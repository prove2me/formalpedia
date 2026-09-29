-- Prove2me | Theorems.Thm_Freiman_form_orbit_lattice_lower_bound
-- name    : Freiman.form_orbit_lattice_lower_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:06.352026+00:00
-- url     : https://prove2.me/theorems/966b91c1-f3be-4cd7-8dba-df71d9d0c3fa
-- title:
--   The reciprocal infimum bounds every lattice vector
-- statement:
--   Apply well-founded descent with the independently stated axis bound and the two explicit signed coordinate updates.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, proof of found:form-minimum

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_orbit_lattice_lower_bound (R : ReducedOrbit) :
    ∀ n p q : ℤ, (p ≠ 0 ∨ q ≠ 0) → orbitReciprocalInfimum R ≤ |reducedValue (R.alpha n) (R.beta n) p q| := by
  sorry

end Freiman
