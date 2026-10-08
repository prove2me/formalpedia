-- Prove2me | Theorems.Thm_OAI_Problem358_one_third_exponent_is_sharp
-- name    : OAI.Problem358.one_third_exponent_is_sharp
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:11.274982+00:00
-- url     : https://prove2.me/theorems/34779274-1ece-457f-993c-1317dcbb7f9c
-- statement:
--   The theorem states that the exponent 1/3 in the companion Brenier-map stability estimate cannot be improved. For every dimension n ≥ 2, every real exponent p > 1/3, and every constant C > 0, there exist two Borel probability measures μ and ν on Euclidean space ℝⁿ and maps T and S from ℝⁿ to itself with the following properties. Both measures are supported in the cube [−1,1]ⁿ, meaning the complement of the cube is null, and each is a finitely supported measure with exactly three atoms in the cube: three distinct points carrying strictly positive weights that sum to 1. The measures are different. Writing λ for normalized Lebesgue measure on the cube, T is the unique quadratic optimal map from λ to μ and S is the unique quadratic optimal map from λ to ν. Here a quadratic optimal map is a measurable map pushing λ forward to the target whose graph coupling minimizes the cost ∫|x−y|² among all couplings, and uniqueness means any coupling with cost at most that of the graph coupling equals the graph coupling. Finally, the Wasserstein-2 distance W₂(μ,ν), defined as the square root of the infimum of the quadratic coupling cost, is strictly positive, and C·W₂(μ,ν)^p is strictly smaller than the L²(λ) distance between the maps, namely the square root of ∫|T(x)−S(x)|² dλ(x).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Brenier.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Brenier.lean; bytes 3817..4793
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_Brenier

namespace OAI

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal

namespace Problem358

theorem one_third_exponent_is_sharp :
    ∀ (dimension : ℕ), 2 ≤ dimension → ∀ exponent : ℝ, (1 / 3 : ℝ) < exponent →
      ∀ constant : ℝ, 0 < constant →
        ∃ (first second : Measure (E dimension)) (firstMap secondMap : E dimension → E dimension),
          IsProbabilityMeasure first ∧ IsProbabilityMeasure second ∧
          IsSupported first (cube dimension) ∧ IsSupported second (cube dimension) ∧
          HasExactlyThreeAtoms first (cube dimension) ∧
          HasExactlyThreeAtoms second (cube dimension) ∧
          first ≠ second ∧
          IsUniqueQuadraticOptimalMap (uniformMeasure (cube dimension)) first firstMap ∧
          IsUniqueQuadraticOptimalMap (uniformMeasure (cube dimension)) second secondMap ∧
          0 < wasserstein2 first second ∧
          constant * Real.rpow (wasserstein2 first second) exponent <
            mapL2Dist (uniformMeasure (cube dimension)) firstMap secondMap := by
  sorry

end Problem358
end
end OAI
