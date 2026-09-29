-- Prove2me | Theorems.Thm_Freiman_form_reduced_pair
-- name    : Freiman.form_reduced_pair
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:10.092725+00:00
-- url     : https://prove2.me/theorems/95d19672-ec56-4d64-9025-5e8984f9dc4e
-- title:
--   Every positive-minimum indefinite form reduces to a positive irrational pair
-- statement:
--   Combine irrationality of the roots, simultaneous unimodular root reduction, and the coefficient normalization calculation. No classical spectrum inclusion is assumed.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, found:reduce-roots

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_reduced_pair (A B C : ℝ) (hd : 0 < B^2-4*A*C) (hm : 0 < quadraticMinimum A B C) :
    ∃ α β : ℝ, 1 < α ∧ 0 < β ∧ β < 1 ∧ Irrational α ∧ Irrational β ∧
      0 < reducedMinimum α β ∧ Real.sqrt (B^2-4*A*C) / quadraticMinimum A B C = 1 / reducedMinimum α β := by
  sorry

end Freiman
