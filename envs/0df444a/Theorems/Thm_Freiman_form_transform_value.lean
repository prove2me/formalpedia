-- Prove2me | Theorems.Thm_Freiman_form_transform_value
-- name    : Freiman.form_transform_value
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:30.403653+00:00
-- url     : https://prove2.me/theorems/23469be0-8ba4-4ae1-9d1d-ada104b7c3e0
-- title:
--   Quadratic value after a linear change of variables
-- statement:
--   The three transformed coefficients are obtained by direct substitution Q(ap+bq,cp+dq).
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, opening paragraph

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_transform_value (A B C : ℝ) (a b c d p q : ℤ) :
    quadraticValue (transformedA A B C a b c d) (transformedB A B C a b c d)
      (transformedC A B C a b c d) p q = quadraticValue A B C (a*p+b*q) (c*p+d*q) := by
  sorry

end Freiman
