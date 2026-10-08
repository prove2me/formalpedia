-- Prove2me | Theorems.Thm_OAI_InfiniteMatroidCounterexample_separate_covering_packing_counterexamples
-- name    : OAI.InfiniteMatroidCounterexample.separate_covering_packing_counterexamples
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:46.755662+00:00
-- url     : https://prove2.me/theorems/662a1d3e-950f-40d2-8d87-0dc9f4538cf4
-- statement:
--   The theorem states that, on the countable ground type E = ℤ × D (where D is the sigma type of pairs (m, f) with f a Boolean function on Boolean m-tuples), two separate counterexamples exist, one to each of two defined conjectures about pairs of matroids. For a subset F of E and a Boolean-indexed pair of matroids M, a family covering of F means choosing sets I_i, each independent in M i, whose union is F; a family packing means choosing pairwise disjoint sets S_i with each S_i spanning in M i. CoveringConjectureFor F M is the proposition that F has a family covering by M if and only if, for every Y ⊆ F, whenever the restrictions M i ↾ Y admit a family packing, they also admit a family covering of Y. PackingConjectureFor F M says that M admits a family packing if and only if, for every Y ⊆ F, whenever the contractions onto Y (the dual of the restriction of the dual to Y) admit a family covering of Y, they also admit a family packing. The first conjunct asserts there exist F ⊆ E and matroids M true and M false on E, each with ground set exactly F, such that CoveringConjectureFor F M fails. The second asserts, independently, that there exist such F and M with ground set F for which PackingConjectureFor F M fails.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InfiniteMatroidCorollaries.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InfiniteMatroidCorollaries.lean; bytes 5182..5466
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries

namespace OAI

namespace InfiniteMatroidCounterexample

open Set Matroid

theorem separate_covering_packing_counterexamples :
    (∃ (F : Set E) (M : Bool → Matroid E),
      (∀ i, (M i).E = F) ∧ ¬ CoveringConjectureFor F M) ∧
    (∃ (F : Set E) (M : Bool → Matroid E),
      (∀ i, (M i).E = F) ∧ ¬ PackingConjectureFor F M) := by
  sorry

end InfiniteMatroidCounterexample
end OAI
