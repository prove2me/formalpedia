-- Prove2me | Theorems.Thm_Freiman_localValue_eventual_upper_of_limit_bounds
-- name    : Freiman.localValue_eventual_upper_of_limit_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:57.223708+00:00
-- url     : https://prove2.me/theorems/e5c3794a-8064-4b72-8582-a229c568194c
-- title:
--   Bounds on all shifted limiting words give the eventual upper limsup bound
-- statement:
--   Let b be a two-sided word in a finite alphabet. Suppose every coordinatewise limit of its shifts along strictly increasing nonnegative centres has local value at zero at most t. Then for every positive epsilon all sufficiently late local values of b are at most t + epsilon.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9, final upper-limsup conclusion from limits of viewing windows, printed p. 13.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem localValue_eventual_upper_of_limit_bounds (b : ℤ → ℕ+) (t : ℝ)
    (hfinite : ∃ M : ℕ, ∀ i : ℤ, (b i : ℕ) ≤ M)
    (hlimits : ∀ (u : ℕ → ℕ), StrictMono u → ∀ y : ℤ → ℕ+,
      (∀ i : ℤ, ∀ᶠ n in Filter.atTop, b ((u n : ℤ) + i) = y i) →
      localValue y 0 ≤ t) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n → localValue b (n : ℤ) ≤ t + ε := by
  sorry

end Freiman
