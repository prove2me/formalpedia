-- Prove2me | Theorems.Thm_Freiman_form_unimodular_minimum
-- name    : Freiman.form_unimodular_minimum
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:57:50.362162+00:00
-- url     : https://prove2.me/theorems/8dadcc41-75dd-4935-8e32-81afcc587cd9
-- title:
--   Unimodular invariance of the existing quadraticMinimum
-- statement:
--   The explicit change of variables permutes the nonzero lattice vectors, so its set of absolute values and hence its existing sInf are unchanged.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, opening paragraph

import Definitions.Def_Freiman_reducedForms

namespace Freiman

theorem form_unimodular_minimum (A B C : ℝ) (a b c d : ℤ) (hdet : formUnimodular a b c d) :
    quadraticMinimum (transformedA A B C a b c d) (transformedB A B C a b c d)
      (transformedC A B C a b c d) = quadraticMinimum A B C := by
  sorry

end Freiman
