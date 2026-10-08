-- Prove2me | Theorems.Thm_OAI_Problem358_one_third_stability
-- name    : OAI.Problem358.one_third_stability
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:11.430978+00:00
-- url     : https://prove2.me/theorems/b8f8eaff-6364-4e13-b492-77d4e34000f1
-- statement:
--   The theorem states that, for every dimension d ≥ 2, every compact convex set S in d-dimensional Euclidean space with nonempty interior, and every nonempty compact set K in the same space, there is a constant C ≥ 0 such that the following holds for all probability measures μ and ν on that space that are both supported in K, meaning each gives zero mass to the complement of K. There exist maps T_μ and T_ν such that T_μ is the unique quadratic optimal transport map from the uniform measure on S to μ, and T_ν is the unique quadratic optimal transport map from the uniform measure on S to ν, and the L² distance between the maps with respect to the uniform measure on S, namely the square root of the integral of |T_μ(x) − T_ν(x)|² over S, is at most C times W₂(μ,ν)^(1/3), where W₂ is the quadratic Wasserstein distance. Here the uniform measure on S is Lebesgue measure restricted to S and divided by the volume of S. A map is a quadratic optimal map if it is measurable, pushes the source measure forward to the target, and its graph coupling has quadratic cost no larger than any other coupling. It is the unique such map if every coupling of no larger cost equals the graph coupling. W₂ is the square root of the infimum of ∫|x−y|² over couplings of the two measures. The constant C depends only on S and K, and the result is stated as an admitted theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Brenier.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Brenier.lean; bytes 2930..3815
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_Brenier

namespace OAI

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal

namespace Problem358

theorem one_third_stability :
    ∀ (dimension : ℕ) (source container : Set (E dimension)),
      2 ≤ dimension → IsCompact source → Convex ℝ source → (interior source).Nonempty →
      IsCompact container → container.Nonempty →
      ∃ constant : ℝ, 0 ≤ constant ∧
        ∀ (first second : Measure (E dimension)),
          IsProbabilityMeasure first → IsProbabilityMeasure second →
          IsSupported first container → IsSupported second container →
          ∃ firstMap secondMap : E dimension → E dimension,
            IsUniqueQuadraticOptimalMap (uniformMeasure source) first firstMap ∧
            IsUniqueQuadraticOptimalMap (uniformMeasure source) second secondMap ∧
            mapL2Dist (uniformMeasure source) firstMap secondMap ≤
              constant * Real.rpow (wasserstein2 first second) (1 / 3 : ℝ) := by
  sorry

end Problem358
end
end OAI
