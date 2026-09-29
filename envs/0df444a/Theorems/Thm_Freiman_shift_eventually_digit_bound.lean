-- Prove2me | Theorems.Thm_Freiman_shift_eventually_digit_bound
-- name    : Freiman.shift_eventually_digit_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:54.596674+00:00
-- url     : https://prove2.me/theorems/d835e7a3-ae92-42b8-b02b-e169da367515
-- title:
--   Every fixed window eventually enters an eventually bounded right tail
-- statement:
--   If all digits far enough to the right are at most M, then along strictly increasing nonnegative centres every fixed translated coordinate is eventually at most M. No bound on the entire negative half of the original word is assumed.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.2, Theorem 1.3, passage from late bounded digits to centred words, printed p. 8.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem shift_eventually_digit_bound (a : ℤ → ℕ+) (M N : ℕ)
    (hbound : ∀ n : ℕ, N ≤ n → (a (n : ℤ) : ℕ) ≤ M)
    (u : ℕ → ℕ) (hu : StrictMono u) :
    ∀ i : ℤ, ∀ᶠ n in Filter.atTop, (a ((u n : ℤ) + i) : ℕ) ≤ M := by
  sorry

end Freiman
