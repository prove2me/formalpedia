-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_main
-- name    : OAI.NoiselessRegression.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:57.948665+00:00
-- url     : https://prove2.me/theorems/427d1ba2-990c-40f7-9c9a-a9993c634ba6
-- statement:
--   The theorem states that two properties hold together, for a fixed universe level u of the randomness space. The setting is noiseless Gaussian regression of an unknown unit vector s in R^d with a finite-state learner. A learner with parameters d, M, T has 2^M possible memory states and uses internal randomness ω from a space Ω. It reads at most T observations, where the nth sample row x_n has independent standard Gaussian entries in R^d and the label is exactly the inner product ⟨x_n, s⟩ with no noise. An initial choice and then each transition may either continue or stop and set the next memory state, and an output map returns a unit vector estimate from the stopping time and final state; if it never stops, the run ends at time T. A learner is admissible for a probability measure ρ on Ω if its initial choice, transitions, outputs and its overall estimate (for each fixed s, and jointly with s drawn uniformly from the sphere) are almost-everywhere measurable. Its angular error is arccos⟨ŝ, s⟩. Success at accuracy ε means this error is at most ε, and its probability is taken over ρ and the samples. The first property, SubquadraticMemory, says there is a constant c>0 such that for every memory function M(d) that is little-o of d², there is d₀ such that for all d ≥ d₀, all sample budgets T, all ε in (0, 1/10], all probability spaces (Ω, ρ) and all admissible learners with M(d) memory parameter, if the learner succeeds with probability at least 2/3 either for the uniformly random s or for every fixed s, then T ≥ c·d·log(1/ε). The second property, FixedQuadraticMemory, says that for every A₀>0 there are c>0 and d₀ such that for all d ≥ d₀, all M ≤ A₀d², all T, all ε in (0, 1/10], and all admissible learners, if the uniform-sphere success probability is at least 2/3, then T ≥ c·d·log(1/ε). Here c is chosen before M in the first property and depends on A₀ in the second. The proof is admitted with sorry in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NoiselessRegression.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/NoiselessRegression.lean; bytes 4539..4619
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_NoiselessRegression

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

theorem main : SubquadraticMemory.{u} ∧ FixedQuadraticMemory.{u} := by
  sorry

end NoiselessRegression
end
end OAI
