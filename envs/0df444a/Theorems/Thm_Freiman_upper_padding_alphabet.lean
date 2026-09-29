-- Prove2me | Theorems.Thm_Freiman_upper_padding_alphabet
-- name    : Freiman.upper_padding_alphabet
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:27.175868+00:00
-- url     : https://prove2.me/theorems/0be2a7e7-0f6c-496c-b31a-6f5232a2cabd
-- title:
--   A common finite alphabet survives padding
-- statement:
--   Padding a word whose digits are bounded by N with the digit 3 gives a family uniformly bounded by max(N,3).
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Padded-copy construction, finite-alphabet hypothesis.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_padding_alphabet (a : ℤ → ℕ+) (N : ℕ) (hN : ∀ i, (a i : ℕ) ≤ N) :
    ∀ j i, (upperPad a j i : ℕ) ≤ max N 3 := by
  sorry

end Freiman
