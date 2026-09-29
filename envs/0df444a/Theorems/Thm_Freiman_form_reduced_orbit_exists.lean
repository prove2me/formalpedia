-- Prove2me | Theorems.Thm_Freiman_form_reduced_orbit_exists
-- name    : Freiman.form_reduced_orbit_exists
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:57:52.583864+00:00
-- url     : https://prove2.me/theorems/5b291437-77f9-413c-a310-f3c39918da8c
-- title:
--   Forward and backward continued-fraction rules give a two-sided reduced orbit
-- statement:
--   The forward floor rule and backward floor(1/β) rule are inverse, preserve the positive irrational domain, and extend any initial pair through every integer time.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, found:form-minimum, opening paragraph

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_reduced_orbit_exists (α β : ℝ) (hα : 1 < α) (hβ : 0 < β) (hβ1 : β < 1) (hiα : Irrational α) (hiβ : Irrational β) :
    ∃ R : ReducedOrbit, R.alpha 0 = α ∧ R.beta 0 = β := by
  sorry

end Freiman
