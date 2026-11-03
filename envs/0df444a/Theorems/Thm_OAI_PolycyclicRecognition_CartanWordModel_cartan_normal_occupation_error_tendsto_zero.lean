-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_cartan_normal_occupation_error_tendsto_zero
-- name    : OAI.PolycyclicRecognition.CartanWordModel.cartan_normal_occupation_error_tendsto_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:07:51.381122+00:00
-- url     : https://prove2.me/theorems/f9a45168-a480-4c98-9a8d-537ae1f00b2e
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.cartan_normal_occupation_error_tendsto_zero: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.cartan_normal_occupation_error_tendsto_zero` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNormalOccupation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNormalOccupation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule MeasureTheory Filter`, `open scoped Manifold Topology NNReal`):
--
--   ```lean
--   theorem cartan_normal_occupation_error_tendsto_zero
--       [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
--       (hExpG : IsGroupExponential ExpG)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
--       (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--         (M.boxCost T hunimod eW E) β.val)
--       {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
--       (hcost : ∀ w : M.wordList,
--         lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
--       (hgap : (M.bound : ℝ) * hi < c * lo)
--       (X : I → H) (S : Finset (FreeMagma I)) (βD : WordBasisSelections X S)
--       (K : Set (Fin (finrank ℝ H) → ℝ)) {R : ℝ} (hR : 0 ≤ R)
--       (hz : ∀ z ∈ K, ‖z‖ ≤ R)
--       (hdomain : ∀ z ∈ K, eW (heightProjection T.character
--         ((WordBasisSelections.basis X S βD).equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
--           (fun x => (1 - c * δ) • x) '' E)
--       {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
--       (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
--       (ε : ℝ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
--       (k : ℝ → cartanRootIdeal H)
--       (hk : ∀ᶠ r : ℝ in atTop,
--         ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
--           (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) r).equivFun (k r)‖ ≤
--             Real.exp (r * ε r))
--       (ρ : (Fin (finrank ℝ H) → ℝ) → ℝ) (hiρ : Integrable ρ volume)
--       (hpρ : ∀ z, 0 ≤ ρ z) (hmass : ∫ z, ρ z = 1) (hρK : ∀ z, z ∉ K → ρ z = 0)
--       {C : Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)}
--       (hC : MeasurableSet C) (hC0 : volume C ≠ 0) (hCfin : volume C ≠ ⊤)
--       (p : ℝ → NormalizedPair G Λ) (x : ℝ → G) (v : cartanRootIdeal H)
--       (f : C(NormalizedPair G Λ, ℝ)) :
--       let bN := fun r => M.boxBasis T hunimod eW E β (max r 0)
--       let bD := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S βD)
--         (fun i => bracketWordExponent (fun _ : I => 1) (βD.val i)) (max (Real.log r) 0)
--       let chart := fun r => coordinateChartPoint (p r) (x r) F.inclusionN F.inclusionD
--         (F.ExpN ∘ F.N.equiv) (F.ExpD ∘ F.D.equiv) (bN r) (bD r) (F.ExpN (F.N.equiv (k r)))
--       let law := fun r => productOccupationLaw (cellProbabilityMeasure volume C hC0 hCfin)
--         (densityProbabilityMeasure volume ρ hiρ hpρ hmass) (chart r)
--       Tendsto (fun r : ℝ =>
--         (∫ y, f ((F.inclusionN (F.ExpN (F.N.equiv v)))⁻¹ • y) ∂(law r : Measure _)) -
--           ∫ y, f y ∂(law r : Measure _)) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.WordBasisSelections`, `OAI.PolycyclicRecognition.bracketWordExponent`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.exponentialRescaleBasis`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel` and `OAI.PolycyclicRecognition.WordBasisSelections.basis` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.DynkinCoefficients`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput`, `OAI.PolycyclicRecognition.NormalizedPair`, `OAI.PolycyclicRecognition.cellProbabilityMeasure` and `OAI.PolycyclicRecognition.normalizedPairAction` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.densityProbabilityMeasure` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxBasis` and `OAI.PolycyclicRecognition.CartanWordModel.boxCost` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` and `OAI.PolycyclicRecognition.finiteDynkinPolynomial` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.coordinateChartPoint` (definitions bundle `OAIQ093D010` of this split); `OAI.PolycyclicRecognition.productOccupationLaw` (definitions bundle `OAIQ093D011` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_increment_mem_template_sequence` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNormalOccupation.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.cartan_normal_occupation_error_tendsto_zero)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008
import Definitions.Def_OAIQ093D010
import Definitions.Def_OAIQ093D011

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

set_option maxHeartbeats 1000000 in
theorem cartan_normal_occupation_error_tendsto_zero
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) (S : Finset (FreeMagma I)) (βD : WordBasisSelections X S)
    (K : Set (Fin (finrank ℝ H) → ℝ)) {R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ z ∈ K, ‖z‖ ≤ R)
    (hdomain : ∀ z ∈ K, eW (heightProjection T.character
      ((WordBasisSelections.basis X S βD).equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
        (fun x => (1 - c * δ) • x) '' E)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (ε : ℝ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → cartanRootIdeal H)
    (hk : ∀ᶠ r : ℝ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) r).equivFun (k r)‖ ≤
          Real.exp (r * ε r))
    (ρ : (Fin (finrank ℝ H) → ℝ) → ℝ) (hiρ : Integrable ρ volume)
    (hpρ : ∀ z, 0 ≤ ρ z) (hmass : ∫ z, ρ z = 1) (hρK : ∀ z, z ∉ K → ρ z = 0)
    {C : Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)}
    (hC : MeasurableSet C) (hC0 : volume C ≠ 0) (hCfin : volume C ≠ ⊤)
    (p : ℝ → NormalizedPair G Λ) (x : ℝ → G) (v : cartanRootIdeal H)
    (f : C(NormalizedPair G Λ, ℝ)) :
    let bN := fun r => M.boxBasis T hunimod eW E β (max r 0)
    let bD := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S βD)
      (fun i => bracketWordExponent (fun _ : I => 1) (βD.val i)) (max (Real.log r) 0)
    let chart := fun r => coordinateChartPoint (p r) (x r) F.inclusionN F.inclusionD
      (F.ExpN ∘ F.N.equiv) (F.ExpD ∘ F.D.equiv) (bN r) (bD r) (F.ExpN (F.N.equiv (k r)))
    let law := fun r => productOccupationLaw (cellProbabilityMeasure volume C hC0 hCfin)
      (densityProbabilityMeasure volume ρ hiρ hpρ hmass) (chart r)
    Tendsto (fun r : ℝ =>
      (∫ y, f ((F.inclusionN (F.ExpN (F.N.equiv v)))⁻¹ • y) ∂(law r : Measure _)) -
        ∫ y, f y ∂(law r : Measure _)) atTop (𝓝 0) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
