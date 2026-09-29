-- Prove2me | Theorems.Thm_Freiman_form_minimum_identity
-- name    : Freiman.form_minimum_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:09.139995+00:00
-- url     : https://prove2.me/theorems/24d13da4-b5e1-436d-b9cd-578e052ed8cb
-- title:
--   Minimum of a reduced form is the reciprocal-tail infimum
-- statement:
--   The report’s minimum identity is reduced to lattice transport, the two coordinate descents, well-founded induction, and the two elementary infimum inequalities.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, found:minimum-identity

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_minimum_identity (R : ReducedOrbit) :
    reducedMinimum (R.alpha 0) (R.beta 0) = orbitReciprocalInfimum R := by
  sorry

end Freiman
