-- Prove2me | Theorems.Thm_Freiman_integerDistance_of_lt_half
-- name    : Freiman.integerDistance_of_lt_half
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:29.890983+00:00
-- url     : https://prove2.me/theorems/8023277b-1ff7-492f-a129-680725534952
-- title:
--   An integer within one half attains the infimum distance
-- statement:
--   All other integers are at least one away from p, so the integer p strictly minimizes the distance when its error is below one half.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, nearest-integer step of found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem integerDistance_of_lt_half (x : ℝ) (p : ℤ) (h : |x-(p:ℝ)| < 1/2) :
    integerDistance x = |x-(p:ℝ)| := by
  sorry

end Freiman
