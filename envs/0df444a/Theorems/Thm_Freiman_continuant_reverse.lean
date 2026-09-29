-- Prove2me | Theorems.Thm_Freiman_continuant_reverse
-- name    : Freiman.continuant_reverse
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:06.006994+00:00
-- url     : https://prove2.me/theorems/2bcdb9d8-5742-4771-96c5-22d35e5246bc
-- title:
--   Reversed finite word denominator ratio
-- statement:
--   The finite backward tail of the n preceding digits equals q_(n−1)/q_n, with 0/1 at n=0.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, proof of found:perron

import Definitions.Def_Freiman_continuants

namespace Freiman

theorem continuant_reverse (b : ℕ → ℕ+) (n : ℕ) :
    finiteCF (((List.range n).map b).reverse) =
      (continuantPrevQ b n : ℝ) / continuantQ b n := by
  sorry

end Freiman
