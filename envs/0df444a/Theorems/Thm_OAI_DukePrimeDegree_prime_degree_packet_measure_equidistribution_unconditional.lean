-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_prime_degree_packet_measure_equidistribution_unconditional
-- name    : OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:36.353716+00:00
-- url     : https://prove2.me/theorems/d562e878-3b42-4f00-97fb-c8b1e153bfdc
-- statement:
--   The theorem states that, for a natural number d with d+1 prime and d+1 at least 5, and a sequence of totally real number fields K_i, each of degree d+1 over the rationals, with a full lattice M_i in K_i (a rank d+1 free subgroup, given with a basis, that spans K_i over the rationals) and an ordering σ_i of the d+1 real embeddings of K_i, whose multiplier discriminant tends to infinity as i grows, there exists a measure ν on the space X(d+1) = SL_{d+1}(R)/SL_{d+1}(Z) (as a right-coset quotient with the Borel structure) such that three things hold. First, ν is a Haar probability measure: a probability measure invariant under the right action of every element of SL_{d+1}(R). Second, the packet measures packetMeasure(M_i, σ_i) converge weakly to ν, meaning each is a probability measure and the integral of every bounded continuous real function converges to its integral against ν. Third, the set of these packet measures is tight. Here the multiplier discriminant is |disc K_i| times the square of the index of the multiplier order of M_i in the integral elements of K_i. The packet measure of M is a normalized, volume-weighted average of the probability measures on the diagonal-flow orbits through the normalized embedded lattices of all lattices locally homothetic to M at every prime, each twisted by diagonal sign matrices.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DukePrimeDegree.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DukePrimeDegree.lean; bytes 8004..8840
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

/-- Theorem 1.1 as weak convergence of the actual complete packet measures,
including tightness of the entire family. -/
theorem prime_degree_packet_measure_equidistribution_unconditional
    (d : ℕ) (hprime : Nat.Prime (d+1)) (hfive : 5 ≤ d+1)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d+1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i)=d+1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop) :
    ∃ ν : Measure (X (d+1)), IsHaarProbability ν ∧
      WeakProbabilityConvergence (fun i => packetMeasure (M i) (σ i)) ν ∧
      IsTightMeasureSet (Set.range (fun i => packetMeasure (M i) (σ i))) := by
  sorry

end DukePrimeDegree
end OAI
