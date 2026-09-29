-- Prove2me | Theorems.Thm_Freiman_bounded_words_subsequence
-- name    : Freiman.bounded_words_subsequence
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:57.308524+00:00
-- url     : https://prove2.me/theorems/bbe02d76-836a-4a59-a974-67486af2376f
-- title:
--   Diagonal compactness for eventually bounded positive digit words
-- statement:
--   For a sequence of two-sided positive-integer words, suppose each fixed coordinate is eventually at most the same natural number M. There is a strictly increasing subsequence and a two-sided word on digits at most M such that each coordinate of the subsequence eventually equals the corresponding coordinate of the limit word.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.2, Theorem 1.3, diagonal-subsequence argument, printed p. 8; §20.1, Lemma 20.1, printed p. 65.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem bounded_words_subsequence (A : ℕ → ℤ → ℕ+) (M : ℕ)
    (h : ∀ i : ℤ, ∀ᶠ n in Filter.atTop, (A n i : ℕ) ≤ M) :
    ∃ v : ℕ → ℕ, StrictMono v ∧
      ∃ b : ℤ → ℕ+,
        (∀ i : ℤ, (b i : ℕ) ≤ M) ∧
        (∀ i : ℤ, ∀ᶠ n in Filter.atTop, A (v n) i = b i) := by
  sorry

end Freiman
