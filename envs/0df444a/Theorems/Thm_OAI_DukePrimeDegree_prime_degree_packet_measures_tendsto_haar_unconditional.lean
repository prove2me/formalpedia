-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_prime_degree_packet_measures_tendsto_haar_unconditional
-- name    : OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:36.499318+00:00
-- url     : https://prove2.me/theorems/9e89f81a-1fe6-4f19-b23a-02208e93fe90
-- statement:
--   The theorem states that, for a natural number d such that d+1 is prime and at least 5, suppose K_i (i ∈ ℕ) is a sequence of totally real number fields, each of degree d+1 over ℚ, with M_i a full lattice of rank d+1 in K_i (a ℤ-submodule with a ℤ-basis of d+1 elements that spans K_i over ℚ), and σ_i an ordering of the d+1 real embeddings of K_i. Suppose the multiplier discriminant of M_i, namely |disc K_i| times the square of the relative index of the multiplier order of M_i (the elements a with aM_i ⊆ M_i) in the ring of integers of K_i, tends to infinity as i → ∞. Let m be any probability measure on X = SL_{d+1}(ℝ)/SL_{d+1}(ℤ), the space of unimodular lattices, with its Borel structure, which is invariant under the right action of every element of SL_{d+1}(ℝ); that is, m is a Haar probability measure. Then the packet measures of (M_i, σ_i) converge weakly to m, meaning each packet measure is a probability measure and, for every bounded continuous real function f on X, the integral of f against the i-th packet measure tends to the integral of f against m. Here the packet measure is the volume-weighted average of normalized probability measures on the diagonal-flow orbits of the normalized embedded lattices, over the lattices locally homothetic to M_i at every prime and over sign-matrix twists.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DukePrimeDegree.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DukePrimeDegree.lean; bytes 8842..9680
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_DukePrimeDegree

namespace OAI

open MeasureTheory Filter

open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets

universe u

/-- The complete packet measures converge weakly to any specified Haar
probability, in the formulation by bounded continuous test functions. -/
theorem prime_degree_packet_measures_tendsto_haar_unconditional
    (d : ℕ) (hprime : Nat.Prime (d+1)) (hfive : 5 ≤ d+1)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d+1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i)=d+1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop)
    (m : ProbabilityMeasure (X (d+1)))
    (hm : IsHaarProbability (m : Measure (X (d+1)))) :
    WeakProbabilityConvergence (fun i => packetMeasure (M i) (σ i))
      (m : Measure (X (d+1))) := by
  sorry

end DukePrimeDegree
end OAI
