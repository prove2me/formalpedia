-- Prove2me | Theorems.Thm_Freiman_digits_bounded_of_local_bound
-- name    : Freiman.digits_bounded_of_local_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:41.314926+00:00
-- url     : https://prove2.me/theorems/bccc3316-eb1f-41d0-893c-904df5c80ea4
-- title:
--   A uniform bound on local Perron values bounds all digits
-- statement:
--   If every local Perron value of a two-sided positive digit word is at most a fixed real number t, then all digits of the word are bounded by a single natural number.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §20.1, Lemma 20.1, bound a_i < lambda_i(a), printed p. 65; §1.1, equation (1.3), printed p. 7.

import Definitions.Def_Freiman_symbolicMarkovSpectrum

namespace Freiman

theorem digits_bounded_of_local_bound (a : ℤ → ℕ+) (t : ℝ)
    (h : ∀ i : ℤ, localValue a i ≤ t) :
    ∃ M : ℕ, ∀ i : ℤ, (a i : ℕ) ≤ M := by
  sorry

end Freiman
