-- Prove2me | Theorems.Thm_Freiman_form_reduced_discriminant
-- name    : Freiman.form_reduced_discriminant
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:25.908259+00:00
-- url     : https://prove2.me/theorems/6bfc2d81-36ee-4b7d-980e-24ef3fd0ecb2
-- title:
--   A normalized reduced form has discriminant one
-- statement:
--   Expand the displayed reduced coefficients; the numerator is (α+β)², so the discriminant is one.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, found:reduced-form

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_reduced_discriminant (α β : ℝ) (h : α+β ≠ 0) :
    (reducedB α β)^2 - 4*reducedA α β*reducedC α β = 1 := by
  sorry

end Freiman
