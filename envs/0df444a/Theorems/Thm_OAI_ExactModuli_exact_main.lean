-- Prove2me | Theorems.Thm_OAI_ExactModuli_exact_main
-- name    : OAI.ExactModuli.exact_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:39.643144+00:00
-- url     : https://prove2.me/theorems/4446f8eb-f6e5-46e3-aacb-af7395c65eee
-- statement:
--   The theorem states that, for a probability space (Ω, μ) and a norm-closed linear subspace E of L¹(μ) (real scalars) that is infinite-dimensional, satisfies the Daugavet property (every rank-one operator x ↦ x + ℓ(x)v, for continuous linear functionals ℓ and vectors v in E, has norm exactly 1 plus the norm of ℓ(·)v), and has a unit ball that is precompact for convergence in measure (for every ε>0 finitely many elements of L¹(μ) cover the unit ball of E, each element of the ball lying within ε of one of them in the measure distance, the infimum of a>0 with μ{|f−g|>a}<a), three conclusions hold for the norm seminorm of E. First, for every x in E of norm 1 and every t>0, the modulus H(x,t) equals max(t/2, t−1) and D(x,t) equals max(0, t−2). Here H(x,t) is the supremum, over closed finite-codimensional subspaces F of E, of the infimum over y in F with norm at least 1 of (‖x+ty‖+‖x−ty‖)/2 − 1, and D(x,t) is the supremum over such F of the infimum over y in F with norm exactly 1 of ‖x+ty‖ − 1. Second, for every t>0 the averaged modulus, the infimum of H(x,t) over unit vectors x, equals max(t/2, t−1), and the one-sided modulus, the infimum of D(x,t) over unit vectors x, equals max(0, t−2). Third, for every seminorm N on E that is equivalent to the original norm (a‖x‖ ≤ N(x) ≤ b‖x‖ for some positive constants a and b), property AUC fails, where AUC means that the one-sided modulus of N is strictly positive for every t>0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DaugavetModuli.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DaugavetModuli.lean; bytes 2855..3561
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

theorem exact_main {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Submodule ℝ (Lp ℝ 1 μ))
    (_hclosed : IsClosed (E : Set (Lp ℝ 1 μ))) (hdim : ¬ FiniteDimensional ℝ E)
    (hprecompact : MeasurePrecompactBall μ E) (hdaugavet : Daugavet E) :
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
