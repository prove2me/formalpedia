-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_PolarTiledSamplerData_count_le_offset_rate
-- name    : OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.count_le_offset_rate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:49:45.769808+00:00
-- url     : https://prove2.me/theorems/79430544-fa29-4138-88b1-9ad474df26c0
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.count_le_offset_rate: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.count_le_offset_rate` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanTiledOffsetRates.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanTiledOffsetRates.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Set Metric`, `open scoped Manifold Pointwise`):
--
--   ```lean
--   theorem PolarTiledSamplerData.count_le_offset_rate
--       (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
--       (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
--       {ε : ℝ} (hε : 0 < ε) (β : M.ConeIdealBases C)
--       (hβ : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
--       (R : ℝ) (scale : ℕ → ℝ) (φ : ℕ → I ≃ₜ* I)
--       (D : M.PolarTiledSamplerData T F hunimod eW K ExpI ι bN ε β R scale φ)
--       (A : templateSymmetryGroup (M.supportIn T hunimod eW))
--       (bI' : Basis (Fin (finrank ℝ
--         (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))))
--         ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val))))
--       (β' : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A.val)))
--       (hβ' : M.IsMaximizingConeIdealBasis
--         (heightConePreimage T eW (transformedPolarCone K A.val)) bI'
--         ((M.supportIn T hunimod eW).weightSupport
--           (A.val '' normalizedPolarTemplates K ε 2)) β') (n : ℕ) :
--       (D.tiles n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) * Real.exp (scale n *
--         ((M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0) -
--           ∑ j, M.coneIdealWordCost
--             (heightConePreimage T eW (transformedPolarCone K A.val))
--             ((M.supportIn T hunimod eW).weightSupport
--               (A.val '' normalizedPolarTemplates K ε 2)) (β'.val j)))
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.normalizedPolarTemplates` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.transformedPolarCone` (definitions bundle `OAIQ093D005` of this split); `OAI.PolycyclicRecognition.templateSymmetryGroup`, `OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases`, `OAI.PolycyclicRecognition.CartanWordModel.supportIn` and `OAI.PolycyclicRecognition.SupportDatum.templateSupport` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.CartanWordModel.coneIdealWordCost`, `OAI.PolycyclicRecognition.CartanWordModel.coneMixedWords` and `OAI.PolycyclicRecognition.CartanWordModel.heightConePreimage` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.CartanWordModel.polarProbeWidths` (definitions bundle `OAIQ093D014` of this split); `OAI.PolycyclicRecognition.CartanWordModel.ConeIdealBases`, `OAI.PolycyclicRecognition.CartanWordModel.IsMaximizingConeIdealBasis`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealWordList`, `OAI.PolycyclicRecognition.CartanWordModel.coneMixedVector` and `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData` (definitions bundle `OAIQ093D020` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.original_law_offset_nonpos` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanTiledOffsetRates.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.count_le_offset_rate)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D020

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]

local notation "C" => heightConePreimage T eW K

omit [SimplyConnectedSpace G] [Nonempty (Fin M.letterCount)]
    [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
set_option maxHeartbeats 1000000 in
theorem PolarTiledSamplerData.count_le_offset_rate
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    {ε : ℝ} (hε : 0 < ε) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
    (R : ℝ) (scale : ℕ → ℝ) (φ : ℕ → I ≃ₜ* I)
    (D : M.PolarTiledSamplerData T F hunimod eW K ExpI ι bN ε β R scale φ)
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (bI' : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val))))
    (β' : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A.val)))
    (hβ' : M.IsMaximizingConeIdealBasis
      (heightConePreimage T eW (transformedPolarCone K A.val)) bI'
      ((M.supportIn T hunimod eW).weightSupport
        (A.val '' normalizedPolarTemplates K ε 2)) β') (n : ℕ) :
    (D.tiles n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) * Real.exp (scale n *
      ((M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0) -
        ∑ j, M.coneIdealWordCost
          (heightConePreimage T eW (transformedPolarCone K A.val))
          ((M.supportIn T hunimod eW).weightSupport
            (A.val '' normalizedPolarTemplates K ε 2)) (β'.val j))) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
