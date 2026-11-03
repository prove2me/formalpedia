-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_controlled_increment_volume
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_controlled_increment_volume
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:02:15.555509+00:00
-- url     : https://prove2.me/theorems/db72da2b-cc1e-47c4-9f7b-15cebbd060a3
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_controlled_increment_volume: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_controlled_increment_volume` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSeparatedTuples.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSeparatedTuples.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule MeasureTheory Filter Set`, `open scoped Manifold Topology ENNReal`):
--
--   ```lean
--   theorem exists_controlled_increment_volume
--       (hExpG : IsGroupExponential ExpG)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
--       (hchartN : ∀ x, chartN x = F.ExpN x)
--       (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
--       (hchartD : ∀ x, chartD x = F.ExpD x)
--       (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (μ : Measure F.N.carrier) (ν : Measure F.D.carrier)
--       [μ.IsHaarMeasure] [ν.IsHaarMeasure] [SigmaFinite μ] [SigmaFinite ν]
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (γ : M.Bases) (h : ℕ) (E : Fin h → Set W)
--       (hE : ∀ i, IsCompact (E i)) (h0 : ∀ i, (0 : W) ∈ E i) (β : Fin h → M.Bases)
--       (hβ : ∀ i, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--         (M.boxCost T hunimod eW (E i)) (β i).val)
--       (scale RH R η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
--       (hscale : ∀ n, 0 ≤ scale n) (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
--       (hRH : HasSubexponentialUpperBoundSeq scale RH)
--       (hR : HasSubexponentialUpperBoundSeq scale R) (hη : Tendsto η atTop (𝓝 0))
--       (s : ℕ → Finset (Fin h → G))
--       (p : ℕ → (Fin h → G) → (Fin h → F.N.carrier) × (Fin h → F.D.carrier))
--       (U : Set ((Fin h → F.N.carrier) × (Fin h → F.D.carrier))) (hU : IsCompact U)
--       {ρ : ℝ}
--       (hp : ∀ n x, x ∈ s n → ∀ i,
--         F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i)
--       (hsmall : ∀ z ∈ U, dist (1 : Fin h → G)
--         (fun i => F.inclusionN (z.1 i) * F.inclusionD (z.2 i)) < ρ / 2)
--       (hsep : ∀ n x, x ∈ s n → ∀ y, y ∈ s n → x ≠ y → ρ ≤ dist x y)
--       (hd : ∀ n x, x ∈ s n → ∀ i,
--         ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n)
--       (hh : ∀ n x, x ∈ s n → ∀ i,
--         ‖eW (heightProjection T.character
--           (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
--             η n * scale n)
--       (hinc : ∀ n x, x ∈ s n → ∀ i, (prefixCoordinateEquiv h).symm (p n x).1 i ∈
--         M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) (E i) (β i) (scale n) (R n)) :
--       ∃ (Q : Fin h → ℕ → ℝ) (RD : ℕ → ℝ),
--         (∀ i n, 0 ≤ Q i n) ∧ (∀ i, HasSubexponentialUpperBoundSeq scale (Q i)) ∧
--         (∀ n, 0 ≤ RD n) ∧ HasSubexponentialUpperBoundSeq scale RD ∧
--         ∀ n, ∃ I : Set (Fin h → F.N.carrier), IsCompact I ∧ MeasurableSet I ∧
--           ((s n).card : ℝ≥0∞) * ((Measure.pi fun _ : Fin h => μ).prod
--             (Measure.pi fun _ : Fin h => ν)) U ≤
--             (Measure.pi fun _ : Fin h => μ) I *
--               (Measure.pi fun _ : Fin h => ν)
--                 {d | ∀ i, ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (d i))‖ ≤ RD n} ∧
--           (∀ u ∈ I, ∀ i, u i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
--             (E i) (β i) (scale n) (Q i n)) ∧
--           (∀ u ∈ I, ∃ x ∈ s n, ∃ z ∈ U,
--             prefixCoordinateEquiv h u = fun i => (p n x).1 i * F.action ((p n x).2 i) (z.1 i))
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList` and `OAI.PolycyclicRecognition.NilpotentLieModel` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq` and `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.cartanLog` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.prefixCoordinateEquiv` (definitions bundle `OAIQ093D005` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost` and `OAI.PolycyclicRecognition.CartanWordModel.groupBox` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSeparatedTuples.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_controlled_increment_volume)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D004
import Definitions.Def_OAIQ093D005
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [IsTopologicalGroup F.D.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]

set_option maxHeartbeats 1000000 in
theorem exists_controlled_increment_volume
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (μ : Measure F.N.carrier) (ν : Measure F.D.carrier)
    [μ.IsHaarMeasure] [ν.IsHaarMeasure] [SigmaFinite μ] [SigmaFinite ν]
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) (h : ℕ) (E : Fin h → Set W)
    (hE : ∀ i, IsCompact (E i)) (h0 : ∀ i, (0 : W) ∈ E i) (β : Fin h → M.Bases)
    (hβ : ∀ i, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (E i)) (β i).val)
    (scale RH R η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 ≤ scale n) (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) (hη : Tendsto η atTop (𝓝 0))
    (s : ℕ → Finset (Fin h → G))
    (p : ℕ → (Fin h → G) → (Fin h → F.N.carrier) × (Fin h → F.D.carrier))
    (U : Set ((Fin h → F.N.carrier) × (Fin h → F.D.carrier))) (hU : IsCompact U)
    {ρ : ℝ}
    (hp : ∀ n x, x ∈ s n → ∀ i,
      F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i)
    (hsmall : ∀ z ∈ U, dist (1 : Fin h → G)
      (fun i => F.inclusionN (z.1 i) * F.inclusionD (z.2 i)) < ρ / 2)
    (hsep : ∀ n x, x ∈ s n → ∀ y, y ∈ s n → x ≠ y → ρ ≤ dist x y)
    (hd : ∀ n x, x ∈ s n → ∀ i,
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n)
    (hh : ∀ n x, x ∈ s n → ∀ i,
      ‖eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
          η n * scale n)
    (hinc : ∀ n x, x ∈ s n → ∀ i, (prefixCoordinateEquiv h).symm (p n x).1 i ∈
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) (E i) (β i) (scale n) (R n)) :
    ∃ (Q : Fin h → ℕ → ℝ) (RD : ℕ → ℝ),
      (∀ i n, 0 ≤ Q i n) ∧ (∀ i, HasSubexponentialUpperBoundSeq scale (Q i)) ∧
      (∀ n, 0 ≤ RD n) ∧ HasSubexponentialUpperBoundSeq scale RD ∧
      ∀ n, ∃ I : Set (Fin h → F.N.carrier), IsCompact I ∧ MeasurableSet I ∧
        ((s n).card : ℝ≥0∞) * ((Measure.pi fun _ : Fin h => μ).prod
          (Measure.pi fun _ : Fin h => ν)) U ≤
          (Measure.pi fun _ : Fin h => μ) I *
            (Measure.pi fun _ : Fin h => ν)
              {d | ∀ i, ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (d i))‖ ≤ RD n} ∧
        (∀ u ∈ I, ∀ i, u i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
          (E i) (β i) (scale n) (Q i n)) ∧
        (∀ u ∈ I, ∃ x ∈ s n, ∃ z ∈ U,
          prefixCoordinateEquiv h u = fun i => (p n x).1 i * F.action ((p n x).2 i) (z.1 i)) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
