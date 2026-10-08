-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_main_uniform_bounded_height
-- name    : OAI.PolycyclicRecognition.main_uniform_bounded_height
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:05.417577+00:00
-- url     : https://prove2.me/theorems/7d90e8c8-19fe-47a3-86d0-5c6f4c91438d
-- statement:
--   The theorem states that, for a connected, simply connected, finite-dimensional real solvable Lie group R (a second countable Hausdorff smooth Lie group), equipped with a compatible proper left-invariant metric d admitting chains of bounded step whose length is at most a linear function of the distance, the following holds. Suppose the Lie algebra of R carries a basis of size a in which every adjoint operator ad(x) is upper triangular, let χ_i(x) be the i-th diagonal entry of ad(x), so that these characters are linear functionals, and let the height space be the Lie algebra modulo the common kernel of all χ_i. Assume R is unimodular, meaning its Haar measure is right-invariant. Let W be a finite-dimensional real normed space with a linear isomorphism q from the height space onto W. Let Exp be a group exponential, meaning Exp(0)=1, Exp((s+t)v)=Exp(sv)Exp(tv), and the curve t↦Exp(tv) has derivative v at 0, and let π be a group homomorphism from R to the additive group of W such that π(Exp x) equals q applied to the height projection of x for every Lie algebra element x. Then there is a finite subgroup A of the linear automorphisms of W such that, for all K≥1 and C≥0, there is a constant B≥0 with the following property: every self quasi-isometry F of R with constants K and C, that is, F satisfies dist(F x,F y)≤K dist(x,y)+C, dist(x,y)≤K dist(F x,F y)+KC, and every point lies within C of the image, admits some A_F in A such that the norm of π(F g)−(π(F 1)+A_F π(g)) is at most B for every g in R. This is an admitted statement, with its proof left as sorry.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PolycyclicRecognition.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PolycyclicRecognition.lean; bytes 8518..9561
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_PolycyclicRecognition

namespace OAI

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory

open scoped Manifold NNReal

attribute [instance] SimplyConnectedSolvableLieModel.normedAddCommGroup
  SimplyConnectedSolvableLieModel.normedSpace SimplyConnectedSolvableLieModel.finiteDimensional
  SimplyConnectedSolvableLieModel.topologicalSpace SimplyConnectedSolvableLieModel.chartedSpace
  SimplyConnectedSolvableLieModel.group SimplyConnectedSolvableLieModel.lieGroup
  SimplyConnectedSolvableLieModel.t2Space SimplyConnectedSolvableLieModel.simplyConnectedSpace
  SimplyConnectedSolvableLieModel.secondCountableTopology
  SimplyConnectedSolvableLieModel.solvable

/-- One finite slope group controls the height of every self quasi-isometry. -/
theorem main_uniform_bounded_height
    (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier)
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a)
    (huni : ModelIsUnimodular R)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier → R.carrier)
    (hExp : IsGroupExponential Exp) (π : R.carrier →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    letI := d.compatibleMetric
    ∃ A : Subgroup (W ≃ₗ[ℝ] W), Set.Finite (A : Set (W ≃ₗ[ℝ] W)) ∧
      ∀ K C : ℝ, 1 ≤ K → 0 ≤ C → ∃ B : ℝ, 0 ≤ B ∧
        ∀ F : SelfQuasiIsometry R.carrier K C, ∃ AF : A, ∀ g,
          ‖(π (F.toFun g)).toAdd - ((π (F.toFun 1)).toAdd + AF.val (π g).toAdd)‖ ≤ B := by
  sorry

end PolycyclicRecognition
end
end OAI
