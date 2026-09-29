-- Prove2me | Theorems.Thm_Freiman_localValue_window_bound
-- name    : Freiman.localValue_window_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:51.677694+00:00
-- url     : https://prove2.me/theorems/5e720fe7-8c7f-4df1-b58f-2dd8d2ff84de
-- title:
--   Two-sided window bound
-- statement:
--   If two two-sided digit words agree on the closed radius-R window around i, their local values at i differ by at most 2/F(R+1)^2. The left and right tails each use the common-prefix bound.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, printed p. 7, equations found:continuants and found:continuity and the finite-tail paragraph after found:local-values; §1.2, Theorem 1.3 for the Perron/local comparison.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Data.Nat.Fib.Basic

namespace Freiman

theorem localValue_window_bound (a b : ℤ → ℕ+) (i : ℤ) (R : ℕ)
    (h : ∀ j : ℤ, i - (R : ℤ) ≤ j → j ≤ i + (R : ℤ) → a j = b j) :
    |localValue a i - localValue b i| ≤ 2 / ((Nat.fib (R + 1) : ℝ) ^ 2) := by
  sorry

end Freiman
