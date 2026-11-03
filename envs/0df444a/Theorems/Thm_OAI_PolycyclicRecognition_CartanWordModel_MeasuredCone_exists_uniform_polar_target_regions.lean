-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_MeasuredCone_exists_uniform_polar_target_regions
-- name    : OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_uniform_polar_target_regions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:51:13.840593+00:00
-- url     : https://prove2.me/theorems/054e9004-1ad1-4ae8-9b70-3806e88ca712
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_uniform_polar_target_regions (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_uniform_polar_target_regions` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPublishedPolarRegions.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPublishedPolarRegions.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Set MeasureTheory Metric Filter`, `open scoped Manifold BigOperators Topology`):
--
--   ```lean
--   theorem MeasuredCone.exists_uniform_polar_target_regions
--       (hExp : IsGroupExponential Exp)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (hNbij : Function.Bijective F.ExpN) (hDbij : Function.Bijective F.ExpD)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
--       (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
--       (hchartN : ∀ v, chartN v = F.ExpN v)
--       (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
--       (hchartD : ∀ v, chartD v = F.ExpD v)
--       (height : G →* Multiplicative W)
--       (hheight : ∀ v, (height (Exp v)).toAdd = eW (heightProjection T.character v))
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
--           dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
--       {Lheight : ℝ} (hLheight : 0 ≤ Lheight)
--       (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Lheight * dist x y)
--       (K : ProperCone ℝ (StrongDual ℝ W)) (A : W ≃ₗ[ℝ] W)
--       (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
--       (D : M.MeasuredCone F (heightConePreimage T eW (transformedPolarCone K A)))
--       (haarQ : NilpotentExponentialHaarInput D.Q.modelSpace D.Q.carrier)
--       (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (ν : Measure F.D.carrier) [ν.IsHaarMeasure]
--       (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (bI : Basis (Fin (finrank ℝ
--         (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A)))))
--         ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A))))
--       (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
--       {ε : ℝ} (hε : 0 < ε) :
--       let C := heightConePreimage (H := H) T eW (transformedPolarCone K A)
--       let E₁ := A '' normalizedPolarTemplates K ε 0
--       let E₂ := A '' normalizedPolarTemplates K ε 2
--       ∃ (α : F.D.carrier →* MulAut D.Q.carrier) (act : G →* Equiv.Perm D.Q.carrier)
--         (μQ : Measure D.Q.carrier) (c : Fin M.letterCount → ℕ)
--         (β₂ : M.ConeIdealBases C),
--         μQ.IsHaarMeasure ∧
--         (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = D.maps.quotient n * α d q) ∧
--         (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∉
--           transformedPolarCone K A → c i = 0) ∧
--         (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈
--           transformedPolarCone K A → 0 < c i) ∧
--         (∀ g E, μQ (act g '' E) = ENNReal.ofReal (Real.exp
--           ((∑ i, (c i : ℝ) • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
--             (height g).toAdd)) * μQ E) ∧
--         M.IsMaximizingConeIdealBasis C bI ((M.supportIn T hunimod eW).weightSupport E₂) β₂ ∧
--         ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
--           StrictMono scale → Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
--           (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
--           ∀ Cp Clog : ℝ, 0 ≤ Cp → 0 ≤ Clog →
--           ∃ R : MeasuredProbeRegions D.maps.quotient μQ
--             (D.kernelMeasure M F C) ν scale
--             (∑ j, M.coneIdealWordCost C
--               ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)),
--             ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
--             ∀ᶠ n in atTop, R.ControlsTwoPaths
--               (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
--               height cell E₁ E₂ η Cp Clog δ n
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.normalizedPolarTemplates` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.transformedPolarCone` (definitions bundle `OAIQ093D005` of this split); `OAI.PolycyclicRecognition.CartanWordModel.supportIn` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealWordCost`, `OAI.PolycyclicRecognition.CartanWordModel.coneMixedWords` and `OAI.PolycyclicRecognition.CartanWordModel.heightConePreimage` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.MeasuredProbeRegions` and `OAI.PolycyclicRecognition.MeasuredProbeRegions.ControlsTwoPaths` (definitions bundle `OAIQ093D009` of this split); `OAI.PolycyclicRecognition.CartanWordModel.ConeIdealBases`, `OAI.PolycyclicRecognition.CartanWordModel.IsMaximizingConeIdealBasis`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealWordList`, `OAI.PolycyclicRecognition.CartanWordModel.coneMixedVector` and `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.ConeGroupMaps` (definitions bundle `OAIQ093D019` of this split); `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone` and `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.kernelMeasure` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.exists_one_cone_offset_threshold` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPublishedPolarRegions.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_uniform_polar_target_regions)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition

namespace CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory Metric Filter
open scoped Manifold BigOperators Topology

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem MeasuredCone.exists_uniform_polar_target_regions
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hNbij : Function.Bijective F.ExpN) (hDbij : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ v, chartD v = F.ExpD v)
    (height : G →* Multiplicative W)
    (hheight : ∀ v, (height (Exp v)).toAdd = eW (heightProjection T.character v))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Lheight : ℝ} (hLheight : 0 ≤ Lheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Lheight * dist x y)
    (K : ProperCone ℝ (StrongDual ℝ W)) (A : W ≃ₗ[ℝ] W)
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    (D : M.MeasuredCone F (heightConePreimage T eW (transformedPolarCone K A)))
    (haarQ : NilpotentExponentialHaarInput D.Q.modelSpace D.Q.carrier)
    (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure]
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A))))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    {ε : ℝ} (hε : 0 < ε) :
    let C := heightConePreimage (H := H) T eW (transformedPolarCone K A)
    let E₁ := A '' normalizedPolarTemplates K ε 0
    let E₂ := A '' normalizedPolarTemplates K ε 2
    ∃ (α : F.D.carrier →* MulAut D.Q.carrier) (act : G →* Equiv.Perm D.Q.carrier)
      (μQ : Measure D.Q.carrier) (c : Fin M.letterCount → ℕ)
      (β₂ : M.ConeIdealBases C),
      μQ.IsHaarMeasure ∧
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = D.maps.quotient n * α d q) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∉
        transformedPolarCone K A → c i = 0) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈
        transformedPolarCone K A → 0 < c i) ∧
      (∀ g E, μQ (act g '' E) = ENNReal.ofReal (Real.exp
        ((∑ i, (c i : ℝ) • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
          (height g).toAdd)) * μQ E) ∧
      M.IsMaximizingConeIdealBasis C bI ((M.supportIn T hunimod eW).weightSupport E₂) β₂ ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
        (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ Cp Clog : ℝ, 0 ≤ Cp → 0 ≤ Clog →
        ∃ R : MeasuredProbeRegions D.maps.quotient μQ
          (D.kernelMeasure M F C) ν scale
          (∑ j, M.coneIdealWordCost C
            ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)),
          ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∀ᶠ n in atTop, R.ControlsTwoPaths
            (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
            height cell E₁ E₂ η Cp Clog δ n := by
  sorry

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end
