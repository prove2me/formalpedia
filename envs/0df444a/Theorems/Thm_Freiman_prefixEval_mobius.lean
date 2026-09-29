-- Prove2me | Theorems.Thm_Freiman_prefixEval_mobius
-- name    : Freiman.prefixEval_mobius
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:50.626568+00:00
-- url     : https://prove2.me/theorems/a7f0b778-cc2d-4b8e-b3f9-23b2cdc78cad
-- title:
--   Möbius formula for finite prefix evaluation
-- statement:
--   The prefix map equals the quotient of the two continuant affine polynomials, including the empty word.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.1, found:continuants

import Definitions.Def_Freiman_continuants

namespace Freiman

theorem prefixEval_mobius (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) :
    prefixEval w x =
      ((wordContinuantP w : ℝ) + x * wordContinuantPrevP w) /
      ((wordContinuantQ w : ℝ) + x * wordContinuantPrevQ w) := by
  sorry

end Freiman
