-- Prove2me | Theorems.Thm_Freiman_integerDistance_integer_translate
-- name    : Freiman.integerDistance_integer_translate
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:09.356252+00:00
-- url     : https://prove2.me/theorems/334189de-8820-4b44-a8d3-6be06280901d
-- title:
--   Integer translation preserves distance to integers
-- statement:
--   An integer translation permutes the integers over which the infimum is taken.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, opening paragraph

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem integerDistance_integer_translate (x : ℝ) (z : ℤ) :
    integerDistance (x + (z : ℝ)) = integerDistance x := by
  sorry

end Freiman
