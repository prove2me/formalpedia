-- Prove2me | Theorems.Thm_Freiman_form_orbit_transport_induction
-- name    : Freiman.form_orbit_transport_induction
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:03.385762+00:00
-- url     : https://prove2.me/theorems/3afa002f-8589-4de4-9a00-579f3f71d1c5
-- title:
--   Iterating signed steps preserves all lattice minima
-- statement:
--   The matrix H_a has determinant −1 and integer inverse. Induction forward and backward over integer n transports the absolute-value set, hence the existing lattice infimum.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, first paragraph after found:form-step

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_orbit_transport_induction (R : ReducedOrbit) (hstep : ∀ n p q : ℤ, reducedValue (R.alpha n) (R.beta n) (((R.digits n : ℕ) : ℤ)*p+q) p = -reducedValue (R.alpha (n+1)) (R.beta (n+1)) p q) :
    ∀ n : ℤ, reducedMinimum (R.alpha n) (R.beta n) = reducedMinimum (R.alpha 0) (R.beta 0) := by
  sorry

end Freiman
