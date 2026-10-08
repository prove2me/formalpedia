-- Prove2me | Theorems.Thm_OAI_RadialTransition_densityInterval
-- name    : OAI.RadialTransition.densityInterval
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:14.088464+00:00
-- url     : https://prove2.me/theorems/76e2666a-7508-4bdd-a2a3-2209b1af57a9
-- statement:
--   The theorem states that there exist a real number p, a pair potential φ : ℝ≥0 → ℝ (a function of interparticle distance), real constants B, C, η, βc, and a two-variable function f(β,ρ) such that the following hold. First, p>0 and p is the packing density, meaning that the maximal number of points in the cube [0,L]³ in ℝ³ with pairwise distances at least 1, divided by L³, tends to p as L→∞. The potential φ is bounded and continuous, with B>0 and C>0, and is stable with constant B: for every N and every configuration of N points in ℝ³, the total pair energy ∑_{i<j} φ(|xᵢ−xⱼ|) is at least −B·N. It also decays algebraically: |φ(r)| ≤ C·r^(−3−1/32) for all r≥1. Next, η>0, the interval (5p/3−η, 5p/3+η) lies in the positive reals, and βc lies in [7/8, 9/8]. Finally, for every density ρ in (5p/3−η, 5p/3+η), the function β ↦ f(β,ρ) is the canonical free energy of φ at density ρ, meaning that for every β>0 the limit as L→∞ of −log Z/(β L³) equals f(β,ρ), where Z is the partition function of N=⌊ρL³⌋ particles in the cube of side L, namely (1/N!)∫ exp(−β·energy) over the configuration cube. Moreover, β ↦ f(β,ρ) has a strict corner at βc: it has a left derivative dLeft and a right derivative dRight there with dRight<dLeft, and it is not differentiable at βc.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RadialDensityInterval.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RadialDensityInterval.lean; bytes 1904..2450
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_RadialDensityInterval

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal

open Filter MeasureTheory Set

namespace RadialTransition

theorem densityInterval :
    ∃ (p : ℝ) (φ : Potential) (B C η βc : ℝ) (f : ℝ → ℝ → ℝ),
      0 < p ∧ IsPackingDensity p ∧
      IsBoundedPotential φ ∧ Continuous φ ∧
      0 < B ∧ 0 < C ∧ StableWith φ B ∧ AlgebraicDecayWith φ C ∧
      0 < η ∧ Ioo (5*p/3 - η) (5*p/3 + η) ⊆ Ioi 0 ∧
      βc ∈ Icc (7/8:ℝ) (9/8) ∧
      ∀ ρ ∈ Ioo (5*p/3 - η) (5*p/3 + η),
        IsCanonicalFreeEnergy φ ρ (fun β => f β ρ) ∧
        StrictTemperatureCorner (fun β => f β ρ) βc := by
  sorry

end RadialTransition
end
end OAI
