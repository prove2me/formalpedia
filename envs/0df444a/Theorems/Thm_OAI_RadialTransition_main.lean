-- Prove2me | Theorems.Thm_OAI_RadialTransition_main
-- name    : OAI.RadialTransition.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:14.320969+00:00
-- url     : https://prove2.me/theorems/f16feaff-b4bb-45ed-86f2-9488fa5e8b9d
-- statement:
--   The theorem states that there exist a real number p, a pair potential φ : [0,∞) → ℝ, positive constants B and C, a function f : ℝ → ℝ, and a number βc such that the following all hold. First, p > 0 and p is the packing density: the maximal number of points in the cube [0,L]³ in ℝ³ with pairwise Euclidean distances at least 1, divided by L³, tends to p as L → ∞. Second, φ is bounded and continuous. Third, φ is stable with constant B, meaning that for every N and every configuration of N points in ℝ³ the energy, the sum of φ(|xᵢ−xⱼ|) over pairs i<j, is at least −BN. Fourth, φ has algebraic decay with constant C: |φ(r)| ≤ C r^(−3−1/32) for all r ≥ 1. Fifth, f is the canonical free energy of φ at density 5p/3: for every inverse temperature β > 0, with N = ⌊(5p/3)L³⌋ and partition function Z = (1/N!)∫ exp(−β·energy) over configurations of N points in the cube [0,L]³, the quantity −log Z/(βL³) tends to f(β) as L → ∞. Finally, βc lies in the closed interval [7/8, 9/8], and f has a strict corner at βc: f has a left derivative dLeft and a right derivative dRight at βc with dRight < dLeft, and f is not differentiable at βc. The theorem is stated with its proof admitted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RadialTransition.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RadialTransition.lean; bytes 1887..2269
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_RadialTransition

namespace OAI

noncomputable section

open scoped BigOperators NNReal

open Filter MeasureTheory Set

namespace RadialTransition

theorem main :
    ∃ (p : ℝ) (φ : Potential) (B C : ℝ) (f : ℝ → ℝ) (βc : ℝ),
      0 < p ∧ IsPackingDensity p ∧
      IsBoundedPotential φ ∧ Continuous φ ∧
      0 < B ∧ 0 < C ∧ StableWith φ B ∧ AlgebraicDecayWith φ C ∧
      IsCanonicalFreeEnergy φ (5*p/3) f ∧
      βc ∈ Icc (7/8:ℝ) (9/8) ∧ StrictTemperatureCorner f βc := by
  sorry

end RadialTransition
end
end OAI
