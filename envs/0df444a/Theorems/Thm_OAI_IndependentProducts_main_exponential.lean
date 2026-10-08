-- Prove2me | Theorems.Thm_OAI_IndependentProducts_main_exponential
-- name    : OAI.IndependentProducts.main_exponential
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:45.950022+00:00
-- url     : https://prove2.me/theorems/4efc49e4-1bed-4e57-a6db-1ff3ea4c9c6e
-- statement:
--   The theorem states that, for every real t>0, with the multiplier law taken to be the exponential law with density e^{-w} on the positive half-line, the following holds in the space X = productSpan(exponentialLaw), the closed real linear span in L1 of the path products over the tree of finite sequences of positive integers (each nonroot vertex carries an independent exponential coordinate, and a vertex's path product is the product of the coordinates along its nonroot prefixes, with the root giving 1), equipped with its L1 norm. Writing c(K) for the Gaussian excess constant (1/16) times the standard Gaussian expectation of max(|x| - 2K, 0), the averaged asymptotic midpoint modulus of X at t is at least (7t/30)·c(10/t). Here that modulus is the infimum over unit vectors x of the supremum over closed finite-codimensional subspaces F of the infimum over y in F with norm at least 1 of (‖x+ty‖+‖x−ty‖)/2 − 1. The theorem also states that the lower bound (7t/30)·c(10/t) is strictly positive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/IndependentProducts.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/IndependentProducts.lean; bytes 3791..4069
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

theorem main_exponential (t : ℝ) (ht : 0 < t) :
    (7 * t / 30) * excessConstant (10 / t) ≤
      averagedMidpointModulus (productSpan exponentialLaw)
        (normSeminorm ℝ (productSpan exponentialLaw)) t ∧
    0 < (7 * t / 30) * excessConstant (10 / t) := by
  sorry

end IndependentProducts
end
end OAI
