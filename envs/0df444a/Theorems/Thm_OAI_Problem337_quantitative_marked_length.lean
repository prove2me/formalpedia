-- Prove2me | Theorems.Thm_OAI_Problem337_quantitative_marked_length
-- name    : OAI.Problem337.quantitative_marked_length
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:10.017351+00:00
-- url     : https://prove2.me/theorems/6f7d2546-df71-4e42-b9cc-95a3affb0594
-- statement:
--   The theorem states that for every real ε>0 there is a natural number m_ε ≥ 2 such that, for every natural number m ≥ m_ε, there exist a length k and a strictly increasing sequence of positive integers n_0<…<n_{k-1} (each n_i ≥ 1) with ∑ 1/n_i = 1 as a rational sum (a one-expansion, which formally permits the term 1 and so the single-term expansion), such that m occurs among the n_i and k ≤ (257/log 2 + ε)·log(log m). Thus every sufficiently large m appears as a denominator in such an expansion of 1 whose length is bounded by this double-logarithmic quantity. The proof is admitted in the source (sorry).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EgyptianFractions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EgyptianFractions.lean; bytes 2650..2965
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EgyptianFractions

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337

theorem quantitative_marked_length :
    ∀ ε : ℝ, 0 < ε → ∃ mε : ℕ, 2 ≤ mε ∧
  ∀ m : ℕ, mε ≤ m →
    ∃ k : ℕ, ∃ n : Fin k → ℕ,
      IsOneExpansion n ∧
      (∃ i : Fin k, n i = m) ∧
      (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  sorry

end Problem337
end
end OAI
