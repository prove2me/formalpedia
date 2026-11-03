-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_ComplexWeightFactorModel_contMDiff_factorParameter
-- name    : OAI.PolycyclicRecognition.ComplexWeightFactorModel.contMDiff_factorParameter
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T19:28:33.454942+00:00
-- url     : https://prove2.me/theorems/beaa1225-881a-4bee-a45b-091758581800
-- title:
--   OAI.PolycyclicRecognition.ComplexWeightFactorModel.contMDiff_factorParameter: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.ComplexWeightFactorModel.contMDiff_factorParameter` of [lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/ComplexFactorLocalChart.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/ComplexFactorLocalChart.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.ComplexWeightFactorModel`, with `open scoped Manifold ContDiff Topology`):
--
--   ```lean
--   theorem contMDiff_factorParameter (hExp : IsGroupExponential Exp) :
--       ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ F.factorParameter
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.ComplexTriangularAdjoint` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.ComplexWeightFactorModel` (definitions bundle `OAIQ093D014` of this split); `OAI.PolycyclicRecognition.ComplexWeightFactorModel.factorParameter` (definitions bundle `OAIQ093D021` of this split); `OAI.PolycyclicRecognition.IsGroupExponential` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proofs of `OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_triangulable_rotation_model` and `OAI.PolycyclicRecognition.ComplexWeightFactorModel.hasMFDerivAt_factorParameter` of this split import it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/ComplexFactorLocalChart.lean (declaration OAI.PolycyclicRecognition.ComplexWeightFactorModel.contMDiff_factorParameter)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D021

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff Topology

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

theorem contMDiff_factorParameter (hExp : IsGroupExponential Exp) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ F.factorParameter := by
  sorry

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end
