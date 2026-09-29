-- Prove2me | Theorems.Thm_Freiman_shifted_words_subsequence
-- name    : Freiman.shifted_words_subsequence
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:56.810186+00:00
-- url     : https://prove2.me/theorems/5faa1351-c7a2-40e2-8797-7b246d275033
-- title:
--   A convergent subsequence of words centred farther and farther right
-- statement:
--   Words shifted to strictly increasing nonnegative centres have a coordinatewise eventually constant subsequence whenever the original right tail has a finite digit bound. The limit is a two-sided word with the same bound.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.2, Theorem 1.3, diagonal-subsequence argument, printed p. 8.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem shifted_words_subsequence (a : ℤ → ℕ+) (M N : ℕ)
    (hbound : ∀ n : ℕ, N ≤ n → (a (n : ℤ) : ℕ) ≤ M)
    (u : ℕ → ℕ) (hu : StrictMono u) :
    ∃ v : ℕ → ℕ, StrictMono v ∧
      ∃ b : ℤ → ℕ+,
        (∀ i : ℤ, (b i : ℕ) ≤ M) ∧
        (∀ i : ℤ, ∀ᶠ n in Filter.atTop,
          a ((u (v n) : ℤ) + i) = b i) := by
  sorry

end Freiman
