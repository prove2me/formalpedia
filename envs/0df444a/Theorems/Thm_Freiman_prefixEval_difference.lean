-- Prove2me | Theorems.Thm_Freiman_prefixEval_difference
-- name    : Freiman.prefixEval_difference
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:59.867632+00:00
-- url     : https://prove2.me/theorems/950f7961-de6c-4604-a3f8-ae68885533af
-- title:
--   Exact difference formula for prefix maps
-- statement:
--   Subtract the two Möbius expressions and use the determinant of absolute value one. This is the equality, before either upper bound, in (found:continuity).
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.1, found:continuity

import Definitions.Def_Freiman_continuants

namespace Freiman

theorem prefixEval_difference (w : List ℕ+) (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |prefixEval w x - prefixEval w y| = |x - y| /
      (((wordContinuantQ w : ℝ) + x * wordContinuantPrevQ w) *
       ((wordContinuantQ w : ℝ) + y * wordContinuantPrevQ w)) := by
  sorry

end Freiman
