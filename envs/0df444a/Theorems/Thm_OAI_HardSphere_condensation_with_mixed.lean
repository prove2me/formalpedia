-- Prove2me | Theorems.Thm_OAI_HardSphere_condensation_with_mixed
-- name    : OAI.HardSphere.condensation_with_mixed
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:43.490386+00:00
-- url     : https://prove2.me/theorems/7e3e667f-b95d-4751-bfcb-32b610211f1c
-- statement:
--   The theorem states that there exist constants ε₀>0 and c₀>0 such that the following holds for every hard-sphere radius a>0 and density parameter ρ>0 with ρa³<ε₀. Take any sequences of positive particle numbers N(k) and torus side lengths L(k)>0 with N(k)→∞, L(k)→∞ and N(k)/L(k)³→ρ. The N(k) particles live on the three-dimensional torus (ℝ/L(k)ℤ)³, and the allowed configurations are those in which every pair of distinct particles has torus (Euclidean) distance strictly greater than a. A ground vector is a jet, meaning an L² function ψ on configuration space together with its coordinate partial derivatives in L², lying in the closure of smooth compactly supported test functions whose supports lie in the allowed set (the Dirichlet domain). It must be bosonic, that is invariant almost everywhere under permutations of the particles, have L² norm 1, and minimize the energy, the sum of the squared L² norms of all coordinate derivatives, among all such bosonic unit vectors in the domain. The theorem asserts two things. First, for any choice of ground vectors Ψ(k) for each k, the liminf as k→∞ of the occupation of Ψ(k) is at least c₀, where the occupation is (L³)⁻¹ times the integral over the remaining N−1 particle positions of the squared modulus of the integral of ψ over the position of the first particle. Second, for any density operators T(k) (positive, trace one) on the L² space whose support is ground-supported, meaning every unit vector in the orthogonal complement of the kernel of T(k) is the function component of some ground vector, the liminf of the mixed occupation is also at least c₀. The mixed occupation is the trace of T(k) compressed by the continuous linear map that sends ψ to the normalized slice integral (L³)^(-1/2) ∫ψ(x,Y)dx on N−1 particles. In the source this theorem is admitted without proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HardSphere.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HardSphere.lean; bytes 19605..20309
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_HardSphere

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators InnerProductSpace ComplexOrder NNReal

namespace OAI.HardSphere

attribute [local instance] _root_.OAI.HardSphere.groundScalarL2Complete

theorem condensation_with_mixed :
    ∃ε₀ c₀ : ℝ,0<ε₀ ∧ 0<c₀ ∧
    ∀a ρ : ℝ,0<a → 0<ρ → ρ*a^3<ε₀ →
    ∀(N : ℕ→ℕ) (L : ℕ→Length) (hN : ∀k,0<N k),
      Tendsto N atTop atTop → Tendsto (fun k ↦ (L k).val) atTop atTop →
      Tendsto (fun k ↦ (N k:ℝ)/(L k).val^3) atTop (𝓝 ρ) →
      (∀Ψ : (k : ℕ)→Jet (N k) (L k),
        (∀k,IsGroundVector (N k) (L k) a (Ψ k)) →
        c₀≤liminf (fun k ↦ occupation (hN k) (Ψ k).1) atTop) ∧
      (∀T : (k : ℕ)→Density.Operator (ScalarL2 (N k) (L k)),
        (∀k,GroundSupported a (T k)) →
        c₀≤liminf (fun k ↦ mixedOccupation (hN k) (T k)) atTop) := by
  sorry

end OAI.HardSphere
end
