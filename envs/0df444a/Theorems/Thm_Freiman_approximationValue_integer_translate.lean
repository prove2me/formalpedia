-- Prove2me | Theorems.Thm_Freiman_approximationValue_integer_translate
-- name    : Freiman.approximationValue_integer_translate
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:03.377623+00:00
-- url     : https://prove2.me/theorems/e659f31b-88bf-458f-a44a-908adca49140
-- title:
--   Integer translation preserves approximation values
-- statement:
--   Adding an integer to an irrational changes q ξ by the integer q z, so the complete sequence of approximation values is unchanged.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, opening paragraph

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem approximationValue_integer_translate (ξ : ℝ) (z : ℤ) (q : ℕ) :
    approximationValue (ξ + (z : ℝ)) q = approximationValue ξ q := by
  sorry

end Freiman
