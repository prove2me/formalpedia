-- Prove2me | Theorems.Thm_Freiman_form_unimodular_discriminant
-- name    : Freiman.form_unimodular_discriminant
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:05.625745+00:00
-- url     : https://prove2.me/theorems/0d856daa-5ad9-477b-85f0-d0c2e7a17ca4
-- title:
--   Unimodular invariance of the discriminant
-- statement:
--   The discriminant is multiplied by det(G)^2 under substitution, hence remains unchanged for det ±1.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, opening paragraph

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_unimodular_discriminant (A B C : ℝ) (a b c d : ℤ) (hdet : formUnimodular a b c d) :
    (transformedB A B C a b c d)^2 -
      4 * transformedA A B C a b c d * transformedC A B C a b c d = B^2-4*A*C := by
  sorry

end Freiman
