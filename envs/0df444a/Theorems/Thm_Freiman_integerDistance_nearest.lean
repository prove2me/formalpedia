-- Prove2me | Theorems.Thm_Freiman_integerDistance_nearest
-- name    : Freiman.integerDistance_nearest
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:01.517987+00:00
-- url     : https://prove2.me/theorems/e008dbd9-2f95-4599-9692-c47227997f99
-- title:
--   The sInf distance is attained by the rounded integer
-- statement:
--   The nearest-integer distance as defined by sInf is attained at floor(q ξ+1/2).
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, proof of found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem integerDistance_nearest (ξ : ℝ) (q : ℕ) :
    integerDistance ((q : ℝ) * ξ) = |(q : ℝ) * ξ - (nearestNumerator ξ q : ℝ)| := by
  sorry

end Freiman
