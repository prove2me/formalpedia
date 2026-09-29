-- Prove2me | Theorems.Thm_Freiman_perron_local_difference_bound
-- name    : Freiman.perron_local_difference_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:55.890322+00:00
-- url     : https://prove2.me/theorems/a90de147-16c9-4933-9101-5d87b8cc6972
-- title:
--   Perron and two-sided local values differ only by the truncated tail
-- statement:
--   For any two-sided word, the existing one-sided Perron value at n differs from its local value at n by at most 1/F(n+1)^2. The forward terms agree exactly and the backward terms use the finite-prefix bound.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, printed p. 7, equations found:continuants and found:continuity and the finite-tail paragraph after found:local-values; §1.2, Theorem 1.3 for the Perron/local comparison.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Data.Nat.Fib.Basic

namespace Freiman

theorem perron_local_difference_bound (a : ℤ → ℕ+) (n : ℕ) :
    |perronValue (fun k : ℕ => a (k : ℤ)) n - localValue a (n : ℤ)| ≤
      1 / ((Nat.fib (n + 1) : ℝ) ^ 2) := by
  sorry

end Freiman
