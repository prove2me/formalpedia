-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_cover_metric_action_box_bound
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_cover_metric_action_box_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:23:32.443507+00:00
-- url     : https://prove2.me/theorems/6a25cc04-a4fc-42ec-85ca-691efbfefa3a
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_cover_metric_action_box_bound: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_cover_metric_action_box_bound` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanCoverMetricProducts.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanCoverMetricProducts.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open Module LieAlgebra LieModule Set Metric`, `open scoped Manifold`):
--
--   ```lean
--   theorem CartanWordModel.exists_cover_metric_action_box_bound
--       (dS : ProperChainMetric (F.N.carrier ⋊[F.action] F.D.carrier))
--       (dD : ProperChainMetric F.D.carrier)
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (β : M.Bases)
--       (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--         (M.boxCost T hunimod eW (M.samplingPolytope T hunimod eW)) β.val) :
--       letI := dS.compatibleMetric
--       letI := dD.compatibleMetric
--       ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℝ, 1 ≤ r → ∀ d : F.D.carrier, dist 1 d ≤ r →
--         ∀ q : F.N.carrier ⋊[F.action] F.D.carrier, dist 1 q ≤ r →
--         F.action d q.left ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
--           (M.samplingPolytope T hunimod eW) β (A * r) 1
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList` and `OAI.PolycyclicRecognition.NilpotentLieModel` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.semidirectProductTopology` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost` and `OAI.PolycyclicRecognition.CartanWordModel.groupBox` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.CartanWordModel.samplingPolytope` (definitions bundle `OAIQ093D014` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.ProperChainMetric`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection`, `OAI.PolycyclicRecognition.ProperChainMetric.compatibleMetric` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.cartan_cover_controlled_pairs` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanCoverMetricProducts.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_cover_metric_action_box_bound)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D014

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set Metric
open scoped Manifold

attribute [local instance] semidirectProductTopology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (M : CartanWordModel H) (hExp : IsGroupExponential Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (hπcont : Continuous (fun g => (π g).toAdd))

set_option maxHeartbeats 1000000 in
include T hExp hπExp hπcont in
theorem CartanWordModel.exists_cover_metric_action_box_bound
    (dS : ProperChainMetric (F.N.carrier ⋊[F.action] F.D.carrier))
    (dD : ProperChainMetric F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (M.samplingPolytope T hunimod eW)) β.val) :
    letI := dS.compatibleMetric
    letI := dD.compatibleMetric
    ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℝ, 1 ≤ r → ∀ d : F.D.carrier, dist 1 d ≤ r →
      ∀ q : F.N.carrier ⋊[F.action] F.D.carrier, dist 1 q ≤ r →
      F.action d q.left ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        (M.samplingPolytope T hunimod eW) β (A * r) 1 := by
  sorry

end PolycyclicRecognition

end

end OAI
end
