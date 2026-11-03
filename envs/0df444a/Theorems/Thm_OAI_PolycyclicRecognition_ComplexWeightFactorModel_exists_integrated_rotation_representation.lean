-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_ComplexWeightFactorModel_exists_integrated_rotation_representation
-- name    : OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_integrated_rotation_representation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T19:30:30.975205+00:00
-- url     : https://prove2.me/theorems/f5103653-584b-43a2-8e7b-75f32db35ff3
-- title:
--   OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_integrated_rotation_representation (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_integrated_rotation_representation` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/RotationRepresentationIntegration.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/RotationRepresentationIntegration.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.ComplexWeightFactorModel`, with `open scoped Manifold ContDiff`):
--
--   ```lean
--   theorem exists_integrated_rotation_representation (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A) :
--       ∃ ρ : F.SmoothRotationalModification hExp →* Aˣ, Continuous ρ ∧
--         ∀ (x : T.kernelIdeal) (h : H),
--           ρ (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
--             F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) =
--             algebraExpUnit (j (cartanRealShadowEquiv T H x)) *
--               algebraExpUnit (j (cartanRealShadowEquiv T H h))
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.ComplexTriangularAdjoint`, `OAI.PolycyclicRecognition.complexCartanTorus`, `OAI.PolycyclicRecognition.complexifiedSubalgebra`, `OAI.PolycyclicRecognition.complexifiedSubalgebra_isCartan`, `OAI.PolycyclicRecognition.realRotationTorus`, `OAI.PolycyclicRecognition.ComplexTriangularAdjoint.kernelIdeal` and `OAI.PolycyclicRecognition.NilpotentLieModel` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.algebraExpUnit` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.rotationalTwist` and `OAI.PolycyclicRecognition.semidirectProductTopology` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.CartanRealShadow` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ComplexWeightFactorModel` and `OAI.PolycyclicRecognition.ComplexWeightFactorModel.rotationCharacter` (definitions bundle `OAIQ093D014` of this split); `OAI.PolycyclicRecognition.cartanRealShadowEquiv` (definitions bundle `OAIQ093D015` of this split); `OAI.PolycyclicRecognition.ComplexWeightFactorModel.SmoothRotationalModification`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.factorCompactRotationAction` and `OAI.PolycyclicRecognition.ComplexWeightFactorModel.factorCompactRotationAction_invariant` (definitions bundle `OAIQ093D022` of this split); `OAI.PolycyclicRecognition.ComplexWeightFactorModel.cartanFactorToRotation` and `OAI.PolycyclicRecognition.ComplexWeightFactorModel.nilpotentFactorToRotation` (definitions bundle `OAIQ093D023` of this split); `OAI.PolycyclicRecognition.IsGroupExponential` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_faithful_rotation_triangular_representation` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/RotationRepresentationIntegration.lean (declaration OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_integrated_rotation_representation)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D023

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem exists_integrated_rotation_representation (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A) :
    ∃ ρ : F.SmoothRotationalModification hExp →* Aˣ, Continuous ρ ∧
      ∀ (x : T.kernelIdeal) (h : H),
        ρ (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
          F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) =
          algebraExpUnit (j (cartanRealShadowEquiv T H x)) *
            algebraExpUnit (j (cartanRealShadowEquiv T H h)) := by
  sorry

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end
