-- Prove2me | Theorems.Thm_OAI_ExactModuli_kadets_werner_existence
-- name    : OAI.ExactModuli.kadets_werner_existence
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:39.800228+00:00
-- url     : https://prove2.me/theorems/6599f35c-aee7-4376-befc-b231b56695ce
-- statement:
--   The theorem states that, on the countable product kwMeasure of unit intervals ℕ → [0,1] (the infinite product of Lebesgue measure on [0,1], a probability space), there exists a real linear subspace E of the real space L¹ with the following five properties. E is closed in the L¹ norm topology, and E is not finite-dimensional. E satisfies MeasurePrecompactBall: for every ε>0 there is a finite set s of L¹ classes such that every y in E with ‖y‖≤1 lies within measureDistance less than ε of some member of s, where the distance between f and g is the infimum of positive a such that the measure of {ω : |f(ω)−g(ω)|>a} is less than a (a convergence-in-measure distance), so the L¹ unit ball of E is totally bounded for convergence in measure. E has the UnitSliceProperty: for every unit vector w in E, every continuous linear functional ℓ on E and real α such that some u in E with ‖u‖≤1 has α<ℓ(u), and every ρ>0, there is a unit vector y in E with α<ℓ(y) and ‖w+y‖≥2−ρ. Finally E has the Daugavet property in the stated form: for every continuous linear functional ℓ on E and every v in E, the identity plus the rank-one operator x↦ℓ(x)v has norm 1 plus the norm of that rank-one operator.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DaugavetModuli.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DaugavetModuli.lean; bytes 3563..3820
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_DaugavetModuli

namespace OAI

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology

universe uX u_1

namespace ExactModuli

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω)

theorem kadets_werner_existence :
    ∃ E : Submodule ℝ (Lp ℝ 1 kwMeasure),
      IsClosed (E : Set (Lp ℝ 1 kwMeasure)) ∧ (¬ FiniteDimensional ℝ E) ∧
      MeasurePrecompactBall kwMeasure E ∧ UnitSliceProperty E ∧ Daugavet E := by
  sorry

end ExactModuli
end
end OAI
