-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_polynomialBoundedChainPacking_intrinsic
-- name    : OAI.PolycyclicRecognition.polynomialBoundedChainPacking_intrinsic
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:48:30.930438+00:00
-- url     : https://prove2.me/theorems/1e155423-6922-42ec-8cdc-1b7264db059b
-- title:
--   OAI.PolycyclicRecognition.polynomialBoundedChainPacking_intrinsic: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.polynomialBoundedChainPacking_intrinsic` of [lean/OAI/GroupTheory/PolycyclicRecognition/Analysis/IntrinsicKernelPacking.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Analysis/IntrinsicKernelPacking.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open PositiveTriangular`, `open scoped Manifold Matrix.Norms.Operator`):
--
--   ```lean
--   theorem polynomialBoundedChainPacking_intrinsic
--       {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
--       (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
--       (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
--       (he : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
--       PolynomialBoundedChainPacking (fun g => (π g).toAdd)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.PolynomialBoundedChainPacking` (definitions bundle `OAIQ093D009` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.recognition_and_lattice_of_uniform_normalized_height_proved` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Analysis/IntrinsicKernelPacking.lean (declaration OAI.PolycyclicRecognition.polynomialBoundedChainPacking_intrinsic)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D009

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition

open PositiveTriangular
open scoped Manifold Matrix.Norms.Operator

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem polynomialBoundedChainPacking_intrinsic
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (he : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    PolynomialBoundedChainPacking (fun g => (π g).toAdd) := by
  sorry

end PolycyclicRecognition

end

end OAI
end
