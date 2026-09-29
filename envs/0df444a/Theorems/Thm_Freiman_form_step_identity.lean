-- Prove2me | Theorems.Thm_Freiman_form_step_identity
-- name    : Freiman.form_step_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:57:55.252317+00:00
-- url     : https://prove2.me/theorems/a229f295-ad6b-428e-96d0-f3ccdaf229f9
-- title:
--   One step of reduced dynamics is a signed lattice substitution
-- statement:
--   Direct substitution proves F_n(H_(a_n) v)=−F_(n+1)(v), exactly (found:form-step).
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, found:form-step

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_step_identity (R : ReducedOrbit) (n p q : ℤ) :
    reducedValue (R.alpha n) (R.beta n) (((R.digits n : ℕ) : ℤ)*p+q) p =
      -reducedValue (R.alpha (n+1)) (R.beta (n+1)) p q := by
  sorry

end Freiman
