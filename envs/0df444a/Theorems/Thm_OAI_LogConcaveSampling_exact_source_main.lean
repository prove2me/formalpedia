-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_exact_source_main
-- name    : OAI.LogConcaveSampling.exact_source_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:54.182122+00:00
-- url     : https://prove2.me/theorems/e63761aa-9c7e-438b-afb0-050c2892e625
-- statement:
--   The theorem states three things about queryComplexity(d), the least integer number q of first-order oracle queries (each reply being the pair V(x), ∇V(x)) for which some randomized adaptive algorithm can output a sample within total-variation distance 1/10 of the Gibbs law proportional to exp(−V) on d-dimensional Euclidean space, uniformly over all C² potentials V with V(0)=0, ∇V(0)=0 and Hessian between the identity and twice the identity, with the value infinite if no budget works. First, for every ε>0 there is a real constant C such that for every dimension d≥2, queryComplexity(d), viewed in the extended nonnegative reals, is at most C·d^ε. Second, there exist c>0 and d₀≥2 such that for all d≥d₀, queryComplexity(d) is at least c·log d. Third, gammaStar, defined as the infimum of all exponents γ≥0 for which queryComplexity(d) is eventually at most d^(γ+ε) for every ε>0, equals 0. The statement is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LogConcaveQuery.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LogConcaveQuery.lean; bytes 3314..3694
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_LogConcaveQuery

namespace OAI

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace LogConcaveSampling

theorem exact_source_main :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d →
      (queryComplexity d).toENNReal ≤ ENNReal.ofReal (C * (d : ℝ) ^ ε)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ENNReal.ofReal (c * Real.log (d : ℝ)) ≤ (queryComplexity d).toENNReal) ∧
    gammaStar = 0 := by
  sorry

end LogConcaveSampling
end
end OAI
