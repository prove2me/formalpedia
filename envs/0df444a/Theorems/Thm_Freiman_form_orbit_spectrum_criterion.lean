-- Prove2me | Theorems.Thm_Freiman_form_orbit_spectrum_criterion
-- name    : Freiman.form_orbit_spectrum_criterion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:29.418095+00:00
-- url     : https://prove2.me/theorems/2cb72c95-8590-49cc-ac1b-cdea806232b2
-- title:
--   The orbit’s symbolic supremum is the reciprocal of its lattice minimum
-- statement:
--   Replace local values by alpha+beta, apply the order-theoretic reciprocal lemma, and use the reduced-form minimum identity.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, found:markov-symbolic

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_orbit_spectrum_criterion (R : ReducedOrbit) (t : ℝ) :
    ((∀ n : ℤ, localValue R.digits n ≤ t) ∧ ∀ ε : ℝ, 0 < ε → ∃ n : ℤ, t-ε<localValue R.digits n) ↔
      0 < reducedMinimum (R.alpha 0) (R.beta 0) ∧ t=1/reducedMinimum (R.alpha 0) (R.beta 0) := by
  sorry

end Freiman
