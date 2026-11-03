-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_normalized_polar_samplers
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_normalized_polar_samplers
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T19:03:15.88142+00:00
-- url     : https://prove2.me/theorems/c7d786ca-ac40-487d-adb0-08808000d045
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_normalized_polar_samplers: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_normalized_polar_samplers` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNormalizedPolarSamplers.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNormalizedPolarSamplers.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Set Metric Filter MeasureTheory`, `open scoped Manifold Pointwise Topology`, `open scoped Matrix.Norms.Operator`):
--
--   ```lean
--   theorem exists_normalized_polar_samplers
--       (hExp : IsGroupExponential Exp)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (eI : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EI)) I)
--       (ExpI : GroupLieAlgebra (𝓘(ℝ, EI)) I → I) (hExpI : IsGroupExponential ExpI)
--       (chartI : GroupLieAlgebra (𝓘(ℝ, EI)) I ≃ₜ I) (hchartI : ∀ v, chartI v = ExpI v)
--       (dynkinI : NilpotentDynkinExpansionInput EI I)
--       (haarI : NilpotentExponentialHaarInput EI I)
--       (ι : I →* F.N.carrier) (hι : Function.Injective ι) (hιm : Measurable ι)
--       (hcompat : ∀ v : M.coneWordIdeal C,
--         ι (ExpI (eI v)) = F.ExpN (F.N.equiv (v : cartanRootIdeal H)))
--       (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
--       (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∈ C)
--       (pivot : H) (hpivot : 0 < M.weight i pivot)
--       (c B ε : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B) (hε : 0 < ε) :
--       ∃ (β : M.ConeIdealBases C) (μI : MeasureTheory.Measure I)
--         (hbij : Function.Bijective ExpI)
--         (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
--           ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
--         (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
--           cartanRootIdeal H) (Rbox δ₀ : ℝ),
--         (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
--         M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β ∧
--         μI.IsHaarMeasure ∧ 0 < Rbox ∧ 0 < δ₀ ∧
--         ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
--         ∀ (scale : ℕ → ℝ), StrictMono scale → Tendsto scale atTop atTop →
--         (∀ n, 0 < scale n) →
--         ∀ (radius time : ℕ → ℝ), HasSubexponentialUpperBoundSeq scale radius →
--         (∀ n, |time n| ≤ radius n * Real.exp
--           ((M.weight i pivot + δ * B) * scale n)) →
--         ∀ (S : H → MulAut F.N.carrier),
--         (∀ h v, S h (F.ExpN (F.N.equiv v)) =
--           F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v))) →
--         ∀ (step : ℕ → F.N.carrier),
--         (∀ n, F.inclusionN (step n) = Exp (time n •
--           (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
--         ∃ n₀ : ℕ,
--           let r := fun n => scale (n + n₀)
--           let h := fun n => (r n * (1 - c * δ)) • pivot
--           let tn := fun n => Real.exp (-M.weight i (h n)) * time (n + n₀)
--           let φ := fun n => M.coneIdealLetterAutomorphism C eI ExpI hExpI hbij chartI
--             hchartI dynkinI i (tn n)
--           ∃ D : M.PolarTiledSamplerData T F hunimod eW K (ExpI ∘ eI) ι bN ε β Rbox r φ,
--             D.chain.bQ = bQ ∧ D.chain.lift = lift ∧
--             ∀ n z, ι (φ n z) =
--               (S (h n)).symm (step (n + n₀)) * ι z *
--                 ((S (h n)).symm (step (n + n₀)))⁻¹
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal` and `OAI.PolycyclicRecognition.NilpotentLieModel` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.normalizedPolarTemplates` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` and `OAI.PolycyclicRecognition.CartanWordModel.heightConePreimage` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.CartanWordModel.polarProbeWidths` (definitions bundle `OAIQ093D014` of this split); `OAI.PolycyclicRecognition.cartanIdealWeightDilation`, `OAI.PolycyclicRecognition.CartanWordModel.ConeIdealBases`, `OAI.PolycyclicRecognition.CartanWordModel.IsMaximizingConeIdealBasis` and `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData` and `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData` (definitions bundle `OAIQ093D020` of this split); `OAI.PolycyclicRecognition.CartanWordModel.coneIdealLetterAutomorphism` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_canonical_polar_samplers` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNormalizedPolarSamplers.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_normalized_polar_samplers)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Definitions.Def_OAIQ093D020

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter MeasureTheory
open scoped Manifold Pointwise Topology

variable {EG G W EI I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
  [NormedAddCommGroup EI] [NormedSpace ℝ EI] [FiniteDimensional ℝ EI]
  [ChartedSpace EI I] [LieGroup (𝓘(ℝ, EI)) ⊤ I] [SimplyConnectedSpace I] [T2Space I]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "C" => heightConePreimage T eW K

open scoped Matrix.Norms.Operator

set_option maxHeartbeats 1000000 in
theorem exists_normalized_polar_samplers
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (eI : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EI)) I)
    (ExpI : GroupLieAlgebra (𝓘(ℝ, EI)) I → I) (hExpI : IsGroupExponential ExpI)
    (chartI : GroupLieAlgebra (𝓘(ℝ, EI)) I ≃ₜ I) (hchartI : ∀ v, chartI v = ExpI v)
    (dynkinI : NilpotentDynkinExpansionInput EI I)
    (haarI : NilpotentExponentialHaarInput EI I)
    (ι : I →* F.N.carrier) (hι : Function.Injective ι) (hιm : Measurable ι)
    (hcompat : ∀ v : M.coneWordIdeal C,
      ι (ExpI (eI v)) = F.ExpN (F.N.equiv (v : cartanRootIdeal H)))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∈ C)
    (pivot : H) (hpivot : 0 < M.weight i pivot)
    (c B ε : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ (β : M.ConeIdealBases C) (μI : MeasureTheory.Measure I)
      (hbij : Function.Bijective ExpI)
      (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H) (Rbox δ₀ : ℝ),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
      M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β ∧
      μI.IsHaarMeasure ∧ 0 < Rbox ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ), StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 0 < scale n) →
      ∀ (radius time : ℕ → ℝ), HasSubexponentialUpperBoundSeq scale radius →
      (∀ n, |time n| ≤ radius n * Real.exp
        ((M.weight i pivot + δ * B) * scale n)) →
      ∀ (S : H → MulAut F.N.carrier),
      (∀ h v, S h (F.ExpN (F.N.equiv v)) =
        F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v))) →
      ∀ (step : ℕ → F.N.carrier),
      (∀ n, F.inclusionN (step n) = Exp (time n •
        (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
      ∃ n₀ : ℕ,
        let r := fun n => scale (n + n₀)
        let h := fun n => (r n * (1 - c * δ)) • pivot
        let tn := fun n => Real.exp (-M.weight i (h n)) * time (n + n₀)
        let φ := fun n => M.coneIdealLetterAutomorphism C eI ExpI hExpI hbij chartI
          hchartI dynkinI i (tn n)
        ∃ D : M.PolarTiledSamplerData T F hunimod eW K (ExpI ∘ eI) ι bN ε β Rbox r φ,
          D.chain.bQ = bQ ∧ D.chain.lift = lift ∧
          ∀ n z, ι (φ n z) =
            (S (h n)).symm (step (n + n₀)) * ι z *
              ((S (h n)).symm (step (n + n₀)))⁻¹ := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
