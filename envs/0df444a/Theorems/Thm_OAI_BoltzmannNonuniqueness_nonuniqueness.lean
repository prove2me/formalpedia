-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_nonuniqueness
-- name    : OAI.BoltzmannNonuniqueness.nonuniqueness
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:23.680846+00:00
-- url     : https://prove2.me/theorems/4e4ffef4-7190-46d1-8222-e3c830f91b41
-- statement:
--   The theorem states that, for the periodic hard-sphere Boltzmann equation on the 3-torus (unit-period positions) with velocities in R³, uniqueness fails even among very regular solutions: there is an initial density f₀ on phase space, with velocities supported in a bounded ball (for some R>0, f₀ vanishes almost everywhere where |v|>R), together with two time-evolutions F and G and a time T>0, such that both F and G are admissible global solutions with initial datum f₀ and both satisfy the additional early-time regularity on [0,T], yet F(t) and G(t) differ on a set of positive measure for some t in [0,T]. Admissibility of F means: f₀ and each F(t), t≥0, are almost everywhere nonnegative, strongly measurable, with integrable entropy moment f(1+|v|²+|log f|); F is jointly measurable, equals f₀ almost everywhere at time 0, is weakly continuous in t against bounded measurable test functions, and has locally uniformly bounded entropy moments; the collision gain and loss integrals are finite for almost every point and their quotients by 1+F/M, with M the Maxwellian, are locally integrable in time; F satisfies the renormalized weak formulation for every admissible renormalization and smooth kinetic test function with the initial term built from f₀, and the local mass equation for every smooth mass test; momentum is conserved, energy does not exceed the initial energy, and relative entropy plus time-integrated entropy dissipation never exceeds the initial relative entropy. The early-time regularity means T>0, F is continuous in L¹ on [0,T], and the gain and loss terms are integrable over [0,T] times phase space.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BoltzmannNonuniqueness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BoltzmannNonuniqueness.lean; bytes 9345..9648
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness

namespace OAI

noncomputable section

open MeasureTheory Set Filter

open scoped RealInnerProductSpace ENNReal Topology

namespace BoltzmannNonuniqueness

theorem nonuniqueness :
    ∃ f₀ : Density, BoundedVelocitySupport f₀ ∧
      ∃ (F G : Evolution) (T : ℝ), AdmissibleGlobal f₀ F ∧ AdmissibleGlobal f₀ G ∧
        StrongEarly T F ∧ StrongEarly T G ∧
        ∃ t ∈ Set.Icc 0 T, ¬(F t =ᵐ[MeasureTheory.volume] G t) :=
  sorry

end BoltzmannNonuniqueness
end
end OAI
