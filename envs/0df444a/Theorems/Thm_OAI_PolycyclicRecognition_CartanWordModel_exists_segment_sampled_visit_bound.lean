-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_segment_sampled_visit_bound
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_segment_sampled_visit_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:27:41.262703+00:00
-- url     : https://prove2.me/theorems/d54044d3-b699-4e1f-b981-df08dc766e49
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_segment_sampled_visit_bound: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_segment_sampled_visit_bound` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPivotVisits.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPivotVisits.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra`, `open scoped Manifold`):
--
--   ```lean
--   theorem exists_segment_sampled_visit_bound
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
--       (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
--       (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
--       (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
--       (X : I → H) (S : Finset (FreeMagma I)) (βD : WordBasisSelections X S)
--       (z : Fin (finrank ℝ H) → ℝ) (v : H) {T₀ ρ : ℝ} (hT₀ : 0 ≤ T₀) (hρ : 0 ≤ ρ) :
--       let P := M.supportIn T hunimod eW
--       let w₀ := eW (heightProjection T.character
--         ((WordBasisSelections.basis X S βD).equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G))
--       let u := eW (heightProjection T.character (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))
--       let E := segment ℝ w₀ (w₀ + T₀ • u)
--       let θ := P.segmentSupportTime u T₀
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ n : G, ∀ i b,
--         |b| ≤ 2 * ρ →
--         PathMetricBound (M.sampledDirectionalVisitPath T hExp realize (θ i • v) i n
--           (wordChartPivot X S βD r z) r (P.weightSupport E i) b)
--           (C * r) (C * (1 + Real.log (2 + r))) ∧
--         ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
--           dist (n * Exp (((t * b) * Real.exp (r * P.weightSupport E i)) •
--                 (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
--               (Exp ((wordChartPivot X S βD r z : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G) * Exp (r • (θ i • v : H))))
--             (n * Exp (((t' * b) * Real.exp (r * P.weightSupport E i)) •
--                 (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
--               (Exp ((wordChartPivot X S βD r z : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G) * Exp (r • (θ i • v : H)))) ≤
--             C * Real.log (2 + r)
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.SupportDatum`, `OAI.PolycyclicRecognition.WordBasisSelections`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport`, `OAI.PolycyclicRecognition.WordBasisSelections.basis` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.PathMetricBound` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.CartanWordModel.supportIn` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` and `OAI.PolycyclicRecognition.CartanWordModel.sampledDirectionalVisitPath` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.wordChartPivot` (definitions bundle `OAIQ093D011` of this split); `OAI.PolycyclicRecognition.SupportDatum.segmentSupportTime` (definitions bundle `OAIQ093D015` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPivotVisits.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_segment_sampled_visit_bound)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D015

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

set_option maxHeartbeats 1000000 in
theorem exists_segment_sampled_visit_bound
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (X : I → H) (S : Finset (FreeMagma I)) (βD : WordBasisSelections X S)
    (z : Fin (finrank ℝ H) → ℝ) (v : H) {T₀ ρ : ℝ} (hT₀ : 0 ≤ T₀) (hρ : 0 ≤ ρ) :
    let P := M.supportIn T hunimod eW
    let w₀ := eW (heightProjection T.character
      ((WordBasisSelections.basis X S βD).equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    let u := eW (heightProjection T.character (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    let E := segment ℝ w₀ (w₀ + T₀ • u)
    let θ := P.segmentSupportTime u T₀
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ n : G, ∀ i b,
      |b| ≤ 2 * ρ →
      PathMetricBound (M.sampledDirectionalVisitPath T hExp realize (θ i • v) i n
        (wordChartPivot X S βD r z) r (P.weightSupport E i) b)
        (C * r) (C * (1 + Real.log (2 + r))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        dist (n * Exp (((t * b) * Real.exp (r * P.weightSupport E i)) •
              (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
            (Exp ((wordChartPivot X S βD r z : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G) * Exp (r • (θ i • v : H))))
          (n * Exp (((t' * b) * Real.exp (r * P.weightSupport E i)) •
              (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
            (Exp ((wordChartPivot X S βD r z : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G) * Exp (r • (θ i • v : H)))) ≤
          C * Real.log (2 + r) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
