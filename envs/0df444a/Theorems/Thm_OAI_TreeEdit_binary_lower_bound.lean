-- Prove2me | Theorems.Thm_OAI_TreeEdit_binary_lower_bound
-- name    : OAI.TreeEdit.binary_lower_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:34.195199+00:00
-- url     : https://prove2.me/theorems/014bbf44-abab-489e-82d2-50edb5772618
-- statement:
--   The theorem states that there exist a real constant c>0 and a natural number d₀ such that for every natural number d≥d₀ there is a length n with 1≤n≤d and a finite set W of binary words (lists over Bool) of exactly length n with at least two elements such that growth(c,d)≤binarySetDistortion(W). Here ed is the edit distance on lists, the least number of unit-cost steps (insertion, deletion, or substitution of one symbol at any position) in an edit script, with no restriction on intermediate word lengths. The distortion of a map f from a metric-like space (X,ρ) into the real sequence space ℓ₁ is the product of the supremum of ‖f(x)−f(y)‖/ρ(x,y) and the supremum of ρ(x,y)/‖f(x)−f(y)‖ over pairs x≠y. The quantity c₁(X,ρ) is the infimum of this distortion over all injective maps into ℓ₁, and binarySetDistortion(W) is c₁ of W under edit distance. The growth function is growth(c,d)=exp(c·√(log d · log log d)). So for all large length caps, there are equal-length binary word sets whose optimal ℓ₁ embedding distortion under edit distance is at least this growth. The theorem is stated with its proof admitted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BinaryEditLower.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BinaryEditLower.lean; bytes 1832..2261
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BinaryEditLower

namespace OAI

namespace TreeEdit

universe u

open BinaryLower

/-- The binary lower-bound theorem of OpenAI's September 27, 2026 tree-constructions
manuscript: finite equal-length witnesses for every sufficiently large length cap. -/
theorem binary_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ d ∧
        ∃ W : Finset (Word Bool n), 2 ≤ W.card ∧
          growth c d ≤ binarySetDistortion W := by
  sorry

end TreeEdit
end OAI
