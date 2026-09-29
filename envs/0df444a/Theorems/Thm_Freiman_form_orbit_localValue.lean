-- Prove2me | Theorems.Thm_Freiman_form_orbit_localValue
-- name    : Freiman.form_orbit_localValue
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:14.096821+00:00
-- url     : https://prove2.me/theorems/d75ec9cc-c852-4f29-b098-566bfd0ff737
-- title:
--   The sum of reduced coordinates equals the symbolic local value
-- statement:
--   The forward complete quotient and backward fractional tail are exactly the two terms defining the symbolic local value.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, proof of found:markov-symbolic

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_orbit_localValue (R : ReducedOrbit) (n : ℤ) :
    R.alpha n + R.beta n = localValue R.digits n := by
  sorry

end Freiman
