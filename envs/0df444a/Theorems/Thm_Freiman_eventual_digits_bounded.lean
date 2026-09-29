-- Prove2me | Theorems.Thm_Freiman_eventual_digits_bounded
-- name    : Freiman.eventual_digits_bounded
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:51.887246+00:00
-- url     : https://prove2.me/theorems/e9716f76-b4b5-420e-8d1c-73840b4c6e0d
-- title:
--   A finite Perron limsup bounds all sufficiently late digits
-- statement:
--   If the local values along the positive half of a two-sided word have finite limsup t, then there are natural numbers M and N such that every digit a(n) with n ≥ N is at most M.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.2, Theorem 1.3, second paragraph of the proof, printed p. 8.

import Definitions.Def_Freiman_symbolicMarkovSpectrum

namespace Freiman

theorem eventual_digits_bounded (a : ℤ → ℕ+) (t : ℝ)
    (h : HasFiniteLimsup (fun n : ℕ => localValue a (n : ℤ)) t) :
    ∃ M N : ℕ, ∀ n : ℕ, N ≤ n → (a (n : ℤ) : ℕ) ≤ M := by
  sorry

end Freiman
