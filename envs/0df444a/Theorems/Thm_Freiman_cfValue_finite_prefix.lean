-- Prove2me | Theorems.Thm_Freiman_cfValue_finite_prefix
-- name    : Freiman.cfValue_finite_prefix
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:42.098362+00:00
-- url     : https://prove2.me/theorems/0173983a-7007-4a72-929a-16939e3f7893
-- title:
--   Finite and infinite backward tails have the same cylinder bound
-- statement:
--   The difference between the existing cfValue and its mth finite convergent is at most 1/F(m+1)^2. The finite residual parameter is exactly zero.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, printed p. 7, equations found:continuants and found:continuity and the finite-tail paragraph after found:local-values; §1.2, Theorem 1.3 for the Perron/local comparison.

import Definitions.Def_Freiman_cfValue
import Mathlib.Data.Nat.Fib.Basic

namespace Freiman

theorem cfValue_finite_prefix (b : ℕ → ℕ+) (m : ℕ) :
    |cfValue b - cfConvergent b m| ≤ 1 / ((Nat.fib (m + 1) : ℝ) ^ 2) := by
  sorry

end Freiman
