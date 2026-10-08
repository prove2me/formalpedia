-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_Barker_even_length_eq_two_or_four
-- name    : OAI.CirculantHadamard.Barker.even_length_eq_two_or_four
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:26.26944+00:00
-- url     : https://prove2.me/theorems/e5898d96-5838-4bd7-8b34-08ce99300eb2
-- statement:
--   The theorem states that if h is a finite integer sequence indexed by Fin n, with n a positive even natural number, and h is a Barker sequence, then n = 2 or n = 4. Here the aperiodic autocorrelation at shift k is the sum over j from 0 to n-k-1 of h(j)·h(j+k), and h is Barker when every entry equals 1 or -1 and, for every shift k with 0 < k < n, the absolute value of this autocorrelation is at most 1. So the only even lengths admitting a Barker sequence in this sense are 2 and 4.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EvenBarker.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EvenBarker.lean; bytes 471..619
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EvenBarker

namespace OAI

namespace CirculantHadamard

universe u

namespace Barker

open scoped BigOperators

theorem even_length_eq_two_or_four {n : ℕ} (h : Fin n → ℤ)
    (hnpos : 0 < n) (hn : Even n) (hb : IsBarker h) : n = 2 ∨ n = 4 := by
  sorry

end Barker
end CirculantHadamard
end OAI
