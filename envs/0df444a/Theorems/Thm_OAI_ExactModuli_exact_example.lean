-- Prove2me | Theorems.Thm_OAI_ExactModuli_exact_example
-- name    : OAI.ExactModuli.exact_example
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:39.491214+00:00
-- url     : https://prove2.me/theorems/9b2ec28a-295b-42d1-9f28-1952e5403fef
-- statement:
--   The theorem states that there exists a closed, infinite-dimensional real linear subspace E of L¹(kwMeasure), where kwMeasure is the infinite product of Lebesgue measures on [0,1] over the countable product space [0,1]^ℕ, with the following properties. The unit ball of E is precompact in the convergence-in-measure distance, meaning that for every ε>0 finitely many elements of L¹ cover it up to distance ε. E has the unit slice property: for any unit vector w, any continuous linear functional ℓ and real α such that some vector of norm at most 1 has ℓ(u)>α, and any ρ>0, there is a unit vector y in E with ℓ(y)>α and ‖w+y‖≥2−ρ. E has the Daugavet property: every rank-one operator ℓ⊗v satisfies ‖Id+ℓ⊗v‖=1+‖ℓ⊗v‖. Moreover, for the norm seminorm of E, every unit vector x and every t>0 satisfy H(x,t)=max(t/2,t−1) and D(x,t)=max(0,t−2). Here H and D are the suprema, over closed finite-codimensional subspaces F, of the infima over y in F of the averaged increment (‖x+ty‖+‖x−ty‖)/2−1 with ‖y‖≥1, respectively of ‖x+ty‖−1 with ‖y‖=1. Consequently the averaged modulus equals max(t/2,t−1) and the one-sided modulus equals max(0,t−2), each taken as an infimum over unit vectors, for all t>0. Finally, no seminorm on E that is two-sided equivalent to the original norm is AUC, that is, has positive one-sided modulus for every t>0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DaugavetModuli.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DaugavetModuli.lean; bytes 3822..4482
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

theorem exact_example :
    ∃ E : Submodule ℝ (Lp ℝ 1 kwMeasure),
      IsClosed (E : Set (Lp ℝ 1 kwMeasure)) ∧ (¬ FiniteDimensional ℝ E) ∧
      MeasurePrecompactBall kwMeasure E ∧ UnitSliceProperty E ∧ Daugavet E ∧
      (∀ (x : E), ‖x‖ = 1 → ∀ t : ℝ, 0 < t →
        H (normSeminorm ℝ E) x t = max (t / 2) (t - 1) ∧
        D (normSeminorm ℝ E) x t = max 0 (t - 2)) ∧
      (∀ t : ℝ, 0 < t →
        averagedModulus (normSeminorm ℝ E) t = max (t / 2) (t - 1) ∧
        oneSidedModulus (normSeminorm ℝ E) t = max 0 (t - 2)) ∧
      (∀ N : Seminorm ℝ E, EquivalentNorm N → ¬ AUC N) := by
  sorry

end ExactModuli
end
end OAI
