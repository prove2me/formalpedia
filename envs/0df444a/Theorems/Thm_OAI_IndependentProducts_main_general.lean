-- Prove2me | Theorems.Thm_OAI_IndependentProducts_main_general
-- name    : OAI.IndependentProducts.main_general
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:46.344333+00:00
-- url     : https://prove2.me/theorems/c0a5f0ec-5c02-4108-85ea-94901505da54
-- statement:
--   The theorem states that, for any Borel measure μ on ℝ satisfying the multiplier hypotheses, the closed real L¹ span of the path products is infinite-dimensional, and no equivalent norm on it is AUC. The hypotheses say that μ is a probability measure, almost every value is positive, μ is not almost surely equal to any constant, its mean is 1, and the identity function has a finite second moment (is in L²). Vertices are finite lists of positive integers, a sample assigns a real number to each nonroot vertex, and the product measure is the infinite product of independent copies of μ, one per nonroot vertex. The path product of a vertex v multiplies the sample values at the nonempty prefixes of v, and is 1 for the root. productSpan(μ) is the topological closure, in L¹ of the product measure, of the real linear span of the classes equal almost everywhere to some path product. The theorem concludes first that productSpan(μ) is not finite-dimensional over ℝ. Second, for every seminorm N on productSpan(μ) that is an equivalent norm, meaning there are constants 0<a≤b with a‖x‖≤N(x)≤b‖x‖ for all x, N fails the AUC property, which requires that, for every t>0, the one-sided asymptotic modulus of N at t is strictly positive. That modulus is the infimum over N-unit vectors x of the supremum over closed finite-codimension subspaces F of the infimum of N(x+ty)−1 over y in F with N(y)=1. The statement is given as an admitted theorem without proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/IndependentProducts.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/IndependentProducts.lean; bytes 3535..3789
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_IndependentProducts

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal Topology

universe uX

namespace IndependentProducts

variable (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem main_general (μ : Measure ℝ) (hμ : MultiplierHypotheses μ) :
    ¬ FiniteDimensional ℝ (productSpan μ) ∧
    ∀ N : Seminorm ℝ (productSpan μ),
      IsEquivalentNorm (productSpan μ) N → ¬ IsAUC (productSpan μ) N := by
  sorry

end IndependentProducts
end
end OAI
