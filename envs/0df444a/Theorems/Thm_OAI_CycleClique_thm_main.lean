-- Prove2me | Theorems.Thm_OAI_CycleClique_thm_main
-- name    : OAI.CycleClique.thm_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:33.605999+00:00
-- url     : https://prove2.me/theorems/ee1803b8-eb8f-4413-9f02-5157a2ff4acc
-- statement:
--   The theorem states a cycle-versus-clique Ramsey result. Here a number N has the Ramsey property for (m,n) if every simple graph G on N vertices either contains a copy of the m-cycle C_m (the cycle graph on m vertices embeds in G as a subgraph) or its complement contains a copy of the complete graph K_n; cycleCliqueRamsey(m,n) is the least such N, taken as the infimum of the set of such N. The theorem asserts two things. First, for all integers m and n with n ≤ m, n ≥ 3, and (m,n) ≠ (3,3), the value cycleCliqueRamsey(m,n) (with m and n converted to natural numbers) equals (m−1)(n−1)+1, as an integer identity. Second, cycleCliqueRamsey(3,3) = 6.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CycleCliqueRamsey.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CycleCliqueRamsey.lean; bytes 339..544
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CycleCliqueRamsey

namespace OAI

namespace CycleClique

open scoped SimpleGraph

theorem thm_main :
    (∀ m n : ℤ, n ≤ m → 3 ≤ n → (m, n) ≠ (3, 3) →
      (cycleCliqueRamsey m.toNat n.toNat : ℤ) = (m - 1) * (n - 1) + 1) ∧
    cycleCliqueRamsey 3 3 = 6 := by
  sorry

end CycleClique
end OAI
