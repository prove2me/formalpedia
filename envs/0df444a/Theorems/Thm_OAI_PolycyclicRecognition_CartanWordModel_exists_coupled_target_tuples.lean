-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_coupled_target_tuples
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_coupled_target_tuples
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T19:48:25.820838+00:00
-- url     : https://prove2.me/theorems/780076a0-23dd-4664-a556-0910211a569d
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_coupled_target_tuples: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_coupled_target_tuples` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanCoupledTargetTuples.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanCoupledTargetTuples.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra MeasureTheory Filter Set Metric`, `open scoped Manifold Topology NNReal ENNReal`):
--
--   ```lean
--   theorem exists_coupled_target_tuples
--       (hExpG : IsGroupExponential ExpG)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (E source : Set W) (β γ : M.Bases)
--       (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--         (M.boxCost T hunimod eW E) β.val)
--       (s : Fin M.letterCount → ℝ)
--       (hs : ∀ i, s i ≤ (M.supportIn T hunimod eW).weightSupport E i)
--       {m h c : ℕ} (letters : Fin m → Fin M.letterCount)
--       (aN : DynkinCoefficients c 2)
--       (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
--       (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
--       (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
--       (hR : HasSubexponentialUpperBoundSeq scale R)
--       (ρ : ℝ) (hρ : 1 ≤ ρ) (k₀ : ℕ → F.N.carrier) (k : ℕ → Fin h → F.N.carrier)
--       (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n))
--       (hk : ∀ n i, k n i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n))
--       (rem : RemezPolynomialInput) (hN : 1 ≤ h * finrank ℝ (cartanRootIdeal H))
--       (p₀ : WordLawData (Fin M.letterCount) (finrank ℝ (cartanRootIdeal H)))
--       (hlim : Tendsto (fun r =>
--         let b := M.boxBasis T hunimod eW source γ (scale r)
--         (basisBracket b, fun i => b.equivFun (Real.exp (scale r * s i) • M.letter i))) atTop (𝓝 p₀))
--       (t₀ : Fin (m + m) → ℝ)
--       (hsub : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters p₀) t₀))
--       (Good : ℕ → Set F.N.carrier) (hGood : ∀ n, MeasurableSet (Good n))
--       {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
--       (base : ℕ → G) (pivot : ℕ → F.D.carrier) :
--       let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
--       let Q := fun n => (fun y => y * k₀ n) ''
--         M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1
--       let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
--       let sample := fun n => coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
--         allLetters M.letter s (scale n) (bundleConjugator m (k n))
--       (∀ n, Good n ⊆ Q n) → (∀ n, 0 < (μ (Good n)).toReal) →
--       HasSubexponentialLowerBoundSeq scale (fun n => (μ (Good n)).toReal / (μ (Q n)).toReal) →
--       ∃ (initial : ℕ → F.N.carrier) (S : ℕ → Set (Fin h → F.N.carrier))
--         (t : ℕ → Finset (Fin h → G)),
--         (∀ n, initial n ∈ Good n) ∧ (∀ n, IsCompact (S n)) ∧
--         (∀ n, (↑(t n) : Set (Fin h → G)) ⊆ (fun v => fun i =>
--           basedImage (p n).val.1 (base n * F.inclusionN (initial n) * F.inclusionD (pivot n))
--             (base n * F.inclusionN (v i) * F.inclusionD (pivot n))) '' S n) ∧
--         (∀ n u, u ∈ t n → ∀ v, v ∈ t n → u ≠ v → 1 ≤ dist u v) ∧
--         HasSubexponentialLowerBoundSeq scale (fun n => ((t n).card : ℝ) /
--           Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW source) γ.val))) ∧
--         ∀ᶠ n in atTop, ∀ v ∈ S n, (∀ i, v i ∈ Good n) ∧
--           ∃ z : Fin (h * m + h * m) → ℝ, z ∈ closedBall 0 ρ ∧
--             SwitchSuccessful (fun _ => Good n) 0 (h * m) (initial n)
--               (sampledSwitchParameters (sample n) (h * m) z) ∧
--             v = sourceBundleStateEquiv h (initial n)
--               (fun i => (innerContinuousMulEquiv (k n i)).toHomeomorph.toMeasurableEquiv)
--               (sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
--                 (bundleParameterChart h m) (scale n) z)
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.columnBasisWeight`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.DynkinCoefficients`, `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput`, `OAI.PolycyclicRecognition.NormalizedPair` and `OAI.PolycyclicRecognition.basisBracket` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.HasSubexponentialLowerBoundSeq`, `OAI.PolycyclicRecognition.RemezPolynomialInput`, `OAI.PolycyclicRecognition.SwitchSuccessful` and `OAI.PolycyclicRecognition.WordLawData` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.basedImage`, `OAI.PolycyclicRecognition.bundleConjugator`, `OAI.PolycyclicRecognition.bundleParameterChart`, `OAI.PolycyclicRecognition.coupledRootIntervalSample` and `OAI.PolycyclicRecognition.innerContinuousMulEquiv` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.sourceBundleProduct` and `OAI.PolycyclicRecognition.sourceBundleStateEquiv` (definitions bundle `OAIQ093D005` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost`, `OAI.PolycyclicRecognition.CartanWordModel.groupBox` and `OAI.PolycyclicRecognition.CartanWordModel.supportIn` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` and `OAI.PolycyclicRecognition.finiteDynkinPolynomial` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.differenceAmplitudeWordEndpoint` (definitions bundle `OAIQ093D009` of this split); `OAI.PolycyclicRecognition.sampledSwitchParameters` (definitions bundle `OAIQ093D015` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proofs of `OAI_PolycyclicRecognition_CartanWordModel_exists_coupled_profile_comparison_region`, `OAI_PolycyclicRecognition_CartanWordModel_good_affine_templates_support_le` and `OAI.PolycyclicRecognition.CartanWordModel.good_affine_templates_support_le_m` of this split import it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanCoupledTargetTuples.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_coupled_target_tuples)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D015

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set Metric
open scoped Manifold Topology NNReal ENNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]

set_option maxHeartbeats 1000000 in
theorem exists_coupled_target_tuples
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E source : Set W) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, s i ≤ (M.supportIn T hunimod eW).weightSupport E i)
    {m h c : ℕ} (letters : Fin m → Fin M.letterCount)
    (aN : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (k₀ : ℕ → F.N.carrier) (k : ℕ → Fin h → F.N.carrier)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n))
    (hk : ∀ n i, k n i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n))
    (rem : RemezPolynomialInput) (hN : 1 ≤ h * finrank ℝ (cartanRootIdeal H))
    (p₀ : WordLawData (Fin M.letterCount) (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun r =>
      let b := M.boxBasis T hunimod eW source γ (scale r)
      (basisBracket b, fun i => b.equivFun (Real.exp (scale r * s i) • M.letter i))) atTop (𝓝 p₀))
    (t₀ : Fin (m + m) → ℝ)
    (hsub : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters p₀) t₀))
    (Good : ℕ → Set F.N.carrier) (hGood : ∀ n, MeasurableSet (Good n))
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (base : ℕ → G) (pivot : ℕ → F.D.carrier) :
    let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
    let Q := fun n => (fun y => y * k₀ n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1
    let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
    let sample := fun n => coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
      allLetters M.letter s (scale n) (bundleConjugator m (k n))
    (∀ n, Good n ⊆ Q n) → (∀ n, 0 < (μ (Good n)).toReal) →
    HasSubexponentialLowerBoundSeq scale (fun n => (μ (Good n)).toReal / (μ (Q n)).toReal) →
    ∃ (initial : ℕ → F.N.carrier) (S : ℕ → Set (Fin h → F.N.carrier))
      (t : ℕ → Finset (Fin h → G)),
      (∀ n, initial n ∈ Good n) ∧ (∀ n, IsCompact (S n)) ∧
      (∀ n, (↑(t n) : Set (Fin h → G)) ⊆ (fun v => fun i =>
        basedImage (p n).val.1 (base n * F.inclusionN (initial n) * F.inclusionD (pivot n))
          (base n * F.inclusionN (v i) * F.inclusionD (pivot n))) '' S n) ∧
      (∀ n u, u ∈ t n → ∀ v, v ∈ t n → u ≠ v → 1 ≤ dist u v) ∧
      HasSubexponentialLowerBoundSeq scale (fun n => ((t n).card : ℝ) /
        Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW source) γ.val))) ∧
      ∀ᶠ n in atTop, ∀ v ∈ S n, (∀ i, v i ∈ Good n) ∧
        ∃ z : Fin (h * m + h * m) → ℝ, z ∈ closedBall 0 ρ ∧
          SwitchSuccessful (fun _ => Good n) 0 (h * m) (initial n)
            (sampledSwitchParameters (sample n) (h * m) z) ∧
          v = sourceBundleStateEquiv h (initial n)
            (fun i => (innerContinuousMulEquiv (k n i)).toHomeomorph.toMeasurableEquiv)
            (sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
              (bundleParameterChart h m) (scale n) z) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
