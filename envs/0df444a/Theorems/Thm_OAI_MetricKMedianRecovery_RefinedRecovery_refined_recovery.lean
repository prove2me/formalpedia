-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_RefinedRecovery_refined_recovery
-- name    : OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:56.689986+00:00
-- url     : https://prove2.me/theorems/17fa1abe-d7d4-48e8-a229-e604b667e974
-- statement:
--   The theorem states that for every integer polynomial bound, every real ε>0 and L₀>0, and every rational μ with 0<μ≤1/4 and μ≤ε/12, there is a randomized binary algorithm A, whose running work is polynomial for inputs with distances at most bound(size), such that the following holds. An input is a rational finite metric (clients and facilities disjoint, with clients union facilities the whole point set, integer distances that are positive between distinct points, and a positive budget k) together with an anchor set of exactly k facilities. Work is polynomial in the sense that, for some constant c>0 and exponent d, the total of query length, seed length and Turing-machine time is at most c(size+1)^d(1+log(1/ζ))^d for every bounded input and every failure parameter ζ in (0,1), where size is the number of clients plus facilities. For every such bounded input and every ζ in (0,1), every random seed makes A output a feasible k-median solution, meaning a set of facilities with at most k elements, nonempty if there are clients. Moreover, for every certificate C, namely a set of k facilities of positive cost, a good subset of it injectively mapped by a proxy map into the anchor set, such that reassigning each good center's cluster to its proxy costs at most the clusters' own cost plus μ times the total cost of the set, and with at most L₀ log(size) non-good centers, the fraction of seeds whose output has k-median cost (the sum over clients of the distance to the nearest chosen center) at most (1+2/e+ε) times the cost of C's centers is at least 1−ζ.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KMedianRefinedRecovery.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KMedianRefinedRecovery.lean; bytes 5883..6461
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_KMedianRefinedRecovery

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

theorem refined_recovery :
    ∀ (bound : Polynomial ℕ) (ε L₀ : ℝ) (μ : ℚ),
      0 < ε → 0 < L₀ → 0 < μ → μ ≤ 1/4 → (μ : ℝ) ≤ ε/12 →
      ∃ A : BinaryRandomizedAlgorithm,
        PolynomialWork A bound ∧
        ∀ I : Input, I.Bounded bound → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
          (∀ s : Seed A I ζ, I.metric.Feasible (output A I ζ s)) ∧
          (∀ C : Certificate I μ L₀,
            1 - ζ ≤ successProbability A I ζ
              ((1 + 2 / Real.exp 1 + ε) * (I.metric.cost C.centers : ℝ))) := by
  sorry

end MetricKMedianRecovery.RefinedRecovery
end OAI
