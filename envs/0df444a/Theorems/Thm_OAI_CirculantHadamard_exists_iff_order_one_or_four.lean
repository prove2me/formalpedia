-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_exists_iff_order_one_or_four
-- name    : OAI.CirculantHadamard.exists_iff_order_one_or_four
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:26.448693+00:00
-- url     : https://prove2.me/theorems/0e12bbf7-f1ef-4a88-9793-d0854fa9d14f
-- statement:
--   The theorem states that for every positive integer n, a real circulant Hadamard matrix of order n exists if and only if n = 1 or n = 4. Here a real n×n matrix H, indexed by Fin n, is circulant if there is a function h on Fin n (cyclic indices, subtraction mod n) with H(i,j) = h(j − i) for all i and j. It is a sign Hadamard matrix if every entry equals 1 or −1 and H Hᵀ = n·I, so distinct rows are orthogonal. ExistsRealCirculantHadamard(n) asserts that some real matrix is both circulant and a sign Hadamard matrix.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CirculantHadamard.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CirculantHadamard.lean; bytes 575..704
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CirculantHadamard

namespace OAI

namespace CirculantHadamard

universe u

theorem exists_iff_order_one_or_four (n : ℕ) (hn : 0 < n) :
    ExistsRealCirculantHadamard n ↔ n = 1 ∨ n = 4 := by
  sorry

end CirculantHadamard
end OAI
