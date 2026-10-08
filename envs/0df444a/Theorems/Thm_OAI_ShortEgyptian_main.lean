-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_main
-- name    : OAI.ShortEgyptian.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:21.058103+00:00
-- url     : https://prove2.me/theorems/d229c134-4750-4cb8-9146-c7db216d1e93
-- statement:
--   The theorem states two things, with its proof admitted rather than established here. An expansion of a/b is a list ns of natural numbers that is strictly increasing, has every entry at least 2, and whose reciprocals 1/n sum, in the rationals, to a/b. minLength(a,b) is the infimum of the lengths of such expansions, taken as 0 if none exists, and maxMinLength(b) is the maximum of minLength(a,b) over all a with 1 ≤ a < b. First, for all natural numbers a and b with 1 ≤ a < b, some expansion of a/b exists. Second, there are real constants c₁ > 0 and c₂ > 0 and a natural number b₀ ≥ 2 such that for every b ≥ b₀, c₁·log(log b) ≤ maxMinLength(b) ≤ c₂·log(log b), so the worst-case shortest Egyptian fraction length with denominator b grows like log log b up to constant factors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ShortEgyptianFractions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ShortEgyptianFractions.lean; bytes 465..842
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ShortEgyptianFractions

namespace OAI

namespace ShortEgyptian

theorem main :
    (∀ a b : ℕ, 1 ≤ a → a < b → ∃ ns : List ℕ, IsExpansion a b ns) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ b : ℕ, b₀ ≤ b →
        c₁ * Real.log (Real.log (b : ℝ)) ≤ (maxMinLength b : ℝ) ∧
        (maxMinLength b : ℝ) ≤ c₂ * Real.log (Real.log (b : ℝ)) := by
  sorry

end ShortEgyptian
end OAI
