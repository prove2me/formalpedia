-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_exists_smooth_mean_coordinate_with_small_budget
-- name    : OAI.CircleDomainRigidity.exists_smooth_mean_coordinate_with_small_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:27:56.366206+00:00
-- url     : https://prove2.me/theorems/a113b69d-6bf6-47f3-9a7a-50ed12d87603
-- title:
--   OAI.CircleDomainRigidity.exists_smooth_mean_coordinate_with_small_budget: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.exists_smooth_mean_coordinate_with_small_budget` of [lean/OAI/Analysis/CircleDomains/Selection/SmallMeanCoordinateConstruction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/SmallMeanCoordinateConstruction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Function Filter MeasureTheory`, `open scoped Topology NNReal ENNReal`, `open FiniteTransfer`):
--
--   ```lean
--   theorem exists_smooth_mean_coordinate_with_small_budget
--       (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
--       (hcoarea : PlanarLipschitzFiberCoarea)
--       {G U S M : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hU : IsOpen U)
--       (hdense : Dense U) (hS : IsOpen S) (hM : IsClosed M) (hboundary : frontier M ⊆ U)
--       {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U) (singular : T)
--       (hbS : σ singular ∉ S) (hMS : M \ {σ singular} ⊆ S) (y₀ : Sphere)
--       (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
--       (hfreeU : π '' Gᶜ ⊆ Uᶜ) (hinf : π OnePoint.infty ∉ S)
--       (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
--       (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
--       (g : Sphere → ℝ≥0∞) (hg : Measurable g)
--       (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
--       (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
--       (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
--       (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
--       (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
--       (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
--         (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
--           (fun z : ℂ => π (z : Sphere)) ⁻¹' S)))
--       (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
--       (hstrict : ∀ x ∈ M \ U, ‖F x‖ < 1)
--       (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
--       (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
--       (hmissFree : ∀ x ∈ ((π '' Gᶜ) \ range σ) ∩ S,
--         ∀ᵐ γ : K ∂(η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure K), F x ∉ range γ.val)
--       (hend : ∀ γ : A, σ singular ∈ range γ.val)
--       (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2))
--       (w : T → ℝ≥0∞) (hw : (∑' t, w t ^ 2) < ∞)
--       (hwp : ∀ s, s ≠ singular → (η : Measure A) {γ | σ s ∈ range γ.val} ≤ w s)
--       {R : ℝ} (hR : 0 ≤ R)
--       (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
--       {ξ : ℝ} (hξ : 0 < ξ)
--       (hsmall : (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) + countingSquareNorm w <
--         meanBudgetTolerance B R ξ) :
--       ∃ (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F G U S M (σ singular) π)
--         (C : MaskedCoordinateData G U π σ),
--         (∀ x, |Q.error x| ≤ dustSmoothingTolerance id Uᶜ δ x) ∧
--         C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
--         C.mask = M ∧ C.singular = singular ∧
--         (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
--         (∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
--           C.physical (Complex.equivRealProdCLM z) = Q.physical z) ∧
--         C.sourceStokesBudget R < ξ
--   ```
--
--   **Definitions.** The statement is written with `ContinuousMap.measurableSpace` (definitions bundle `Q146C000` of this split); `OAI.CircleDomainRigidity.PathTime`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.physicalDomainLength`, `OAI.CircleDomainRigidity.sphereBorel` and `OAI.CircleDomainRigidity.sphereMetric` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.PlanarLipschitzFiberCoarea`, `OAI.CircleDomainRigidity.countingSquareNorm`, `OAI.CircleDomainRigidity.dustSmoothingTolerance` and `OAI.CircleDomainRigidity.meanBudgetTolerance` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.diskTerminalArcSet`, `OAI.CircleDomainRigidity.meanPhysicalOccupation`, `OAI.CircleDomainRigidity.periodBandGraph`, `OAI.CircleDomainRigidity.sphericalArea`, `OAI.CircleDomainRigidity.FiniteTransfer.MaskedCoordinateData` and `OAI.CircleDomainRigidity.FiniteTransfer.MaskedCoordinateData.sourceStokesBudget` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.UnitDiskCrosscutSeparation` and `OAI.CircleDomainRigidity.instBorelSpaceSphere_24` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.SmoothMeanPeriodData` (definitions bundle `Q146C007` of this split); `OAI.CircleDomainRigidity.Sphere` and `OAI.CircleDomainRigidity.finiteCoord` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.RecursiveCodeLaw.eventually_protrusion_mean` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/SmallMeanCoordinateConstruction.lean (declaration OAI.CircleDomainRigidity.exists_smooth_mean_coordinate_with_small_budget)

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C007

section

attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r16ac95_1 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_smooth_mean_coordinate_with_small_budget
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U S M : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hU : IsOpen U)
    (hdense : Dense U) (hS : IsOpen S) (hM : IsClosed M) (hboundary : frontier M ⊆ U)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U) (singular : T)
    (hbS : σ singular ∉ S) (hMS : M \ {σ singular} ⊆ S) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (hfreeU : π '' Gᶜ ⊆ Uᶜ) (hinf : π OnePoint.infty ∉ S)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' S)))
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hstrict : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (hmissFree : ∀ x ∈ ((π '' Gᶜ) \ range σ) ∩ S,
      ∀ᵐ γ : K ∂(η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure K), F x ∉ range γ.val)
    (hend : ∀ γ : A, σ singular ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2))
    (w : T → ℝ≥0∞) (hw : (∑' t, w t ^ 2) < ∞)
    (hwp : ∀ s, s ≠ singular → (η : Measure A) {γ | σ s ∈ range γ.val} ≤ w s)
    {R : ℝ} (hR : 0 ≤ R)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hsmall : (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) + countingSquareNorm w <
      meanBudgetTolerance B R ξ) :
    ∃ (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F G U S M (σ singular) π)
      (C : MaskedCoordinateData G U π σ),
      (∀ x, |Q.error x| ≤ dustSmoothingTolerance id Uᶜ δ x) ∧
      C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
      C.mask = M ∧ C.singular = singular ∧
      (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        C.physical (Complex.equivRealProdCLM z) = Q.physical z) ∧
      C.sourceStokesBudget R < ξ := by
  sorry

end CircleDomainRigidity

end

end OAI
end
