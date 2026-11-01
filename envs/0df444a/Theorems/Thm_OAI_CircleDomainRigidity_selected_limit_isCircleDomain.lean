-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_selected_limit_isCircleDomain
-- name    : OAI.CircleDomainRigidity.selected_limit_isCircleDomain
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T05:38:10.850008+00:00
-- url     : https://prove2.me/theorems/bda57ed2-63ec-47a4-88c3-2c4a118f124a
-- title:
--   OAI.CircleDomainRigidity.selected_limit_isCircleDomain: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.selected_limit_isCircleDomain` of [lean/OAI/Analysis/CircleDomains/Topology/SelectedCircleDomain.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Topology/SelectedCircleDomain.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Function Filter MeasureTheory`, `open scoped Topology NNReal ENNReal`, `open FiniteTransfer`):
--
--   ```lean
--   theorem selected_limit_isCircleDomain
--       (hcoarea : PlanarLipschitzFiberCoarea) (hweighted : WeightedPlanarScalarCoarea)
--       (hLusin : FiniteTorusAnalyticMeasurability)
--       (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
--       (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
--       (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
--       (base : PathCodeData Sphere Sphere)
--       (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
--       (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
--       (hdust : base.dust = base.quotientDomainᶜ) (hinftyU : OnePoint.infty ∈ base.quotientDomain)
--       (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
--       (hr : ∀ x y, π x = π y ↔ x = y ∨
--         (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
--       (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
--       (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
--       (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
--       (hinf : OnePoint.infty ∈ base.physicalDomain)
--       (hBimage : base.dust = π '' base.physicalDomainᶜ)
--       (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
--       (harcs : ∀ K : Set Sphere, IsCompact K → LocallyConnectedSpace K →
--         HasSimpleArcsInConnectedOpens K)
--       (E₀ : Set Sphere) (hE₀ : IsCompact E₀) (hE₀U : E₀ ⊆ base.quotientDomain)
--       (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ E₀)
--       (B₀ : Set base.dust)
--       (seed : ℕ → SelectableMaskedCoordinate base π)
--       (seedPresentation : ∀ n, RealCoordinatePresentation base π (seed n).coordinate)
--       (S : ℕ → Set (CoordinateExclusionTest hsch base π B₀ (B / 4)))
--       (q : ℕ → Option (CoordinateExclusionTest hsch base π B₀ (B / 4)))
--       (hpref : ∀ n c, c ∈ S n ↔ ∃ k < n, q k = some c)
--       (hcover : ∀ t, seededMaskedAllowed seed CoordinateExclusionTest.coordinate (⋃ n, S n) t →
--         t.neighborhood ⊆ ⋃ t ∈ ⋃ n, S n, t.neighborhood)
--       (hcompat : let D := orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q
--         ∀ (j : ℕ ⊕ₗ ℕ) (n : ℕ) (labels : Fin n → ℕ ⊕ₗ ℕ), (∀ i, labels i < j) →
--           (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
--             (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
--               (fun k => (D k).coordinate.graph) labels) = 0)
--       (F : SelectedMixedModels hsch base hU hdense π he hBimage
--         (orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q)
--         (orderedSelectedPresentations seed seedPresentation CoordinateExclusionTest.coordinate
--           CoordinateExclusionTest.presentation q) B₀)
--       (A : AssignedMixedModelLimit F.model) (hB : B / 4 < F.model.real.radius)
--       (hBouter : B ≤ 2 * F.model.real.radius)
--       (tests : Set (GradedRealTest base π E₀))
--       (hretained : ∀ b ∈ tests, ∃ (i : ℕ), (seedPresentation i).coordinate = b.coordinate)
--       (htests : ∀ p ∈ base.dust \ (Subtype.val '' B₀),
--         ∀ k, ∃ b ∈ tests, b.grade = k ∧ p ∈ b.region)
--       (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
--       (hderiv : ∀ z : ℂ,
--         ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
--           C₀ / (1 + ‖z‖ ^ 2))
--       (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
--         StandardBorelProbabilityLaws (BasePathCode e))
--       (hpath : PolishProbabilityLaws C(PathTime, Sphere))
--       (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
--       (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
--       (hdual : ∀ (e : PathCodeData Sphere Sphere)
--         (J : Set ℕ) [PolishSpace J] (b : J → Sphere) (c : J → ℝ≥0∞)
--         (ν : Measure Sphere) [IsFiniteMeasure ν]
--         [StandardBorelSpace (ConstrainedCostCode e b c ν)],
--         MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere J))
--       (hlift : ∀ (e : PathCodeData Sphere Sphere)
--         (J : Set ℕ) [PolishSpace J] (b : J → Sphere) (c : J → ℝ≥0∞)
--         (ν : Measure Sphere) [IsFiniteMeasure ν]
--         [StandardBorelSpace (ConstrainedCostCode e b c ν)],
--         MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere J)) :
--       IsCircleDomain (extendAtInfinity A.function '' base.physicalDomain)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.PathCodeData`, `OAI.CircleDomainRigidity.PathTime`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.SmoothPlanarSard`, `OAI.CircleDomainRigidity.TagSlot`, `OAI.CircleDomainRigidity.TaggedPath`, `OAI.CircleDomainRigidity.extendAtInfinity`, `OAI.CircleDomainRigidity.residualImage`, `OAI.CircleDomainRigidity.roundSphereEquiv`, `OAI.CircleDomainRigidity.sphereBorel` and `OAI.CircleDomainRigidity.sphereMetric` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.ExteriorCoefficientAreaTheorem`, `OAI.CircleDomainRigidity.FiniteTorusAnalyticMeasurability`, `OAI.CircleDomainRigidity.HasSimpleArcsInConnectedOpens`, `OAI.CircleDomainRigidity.LevelTuple`, `OAI.CircleDomainRigidity.MeasureImageDuality`, `OAI.CircleDomainRigidity.MeasurePlanLifting`, `OAI.CircleDomainRigidity.PathCostSpace`, `OAI.CircleDomainRigidity.PlanarLipschitzFiberCoarea`, `OAI.CircleDomainRigidity.PolishProbabilityLaws`, `OAI.CircleDomainRigidity.StandardBorelProbabilityLaws`, `OAI.CircleDomainRigidity.TupleType`, `OAI.CircleDomainRigidity.WeightedPlanarScalarCoarea`, `OAI.CircleDomainRigidity.freeComponentFailure`, `OAI.CircleDomainRigidity.instBorelSpacePathCostSpace`, `OAI.CircleDomainRigidity.instMeasurableSpaceLevelTuple`, `OAI.CircleDomainRigidity.instMeasurableSpacePathCostSpaceOfTopologicalSpace`, `OAI.CircleDomainRigidity.instPolishSpacePathCostSpace`, `OAI.CircleDomainRigidity.instTopologicalSpacePathCostSpace`, `OAI.CircleDomainRigidity.tupleReference` and `OAI.CircleDomainRigidity.FiniteTransfer.modelError` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.BasePathCode`, `OAI.CircleDomainRigidity.BorelPathRelationSelection`, `OAI.CircleDomainRigidity.ConstrainedCostCode`, `OAI.CircleDomainRigidity.EndpointCode`, `OAI.CircleDomainRigidity.FiniteCostCode`, `OAI.CircleDomainRigidity.MapDiskData`, `OAI.CircleDomainRigidity.PhysicalRealCoordinate`, `OAI.CircleDomainRigidity.instMeasurableSpaceTagSlot`, `OAI.CircleDomainRigidity.pathCostMeasure`, `OAI.CircleDomainRigidity.FiniteTransfer.AssignedMixedModelLimit`, `OAI.CircleDomainRigidity.FiniteTransfer.MaskedCoordinateData`, `OAI.CircleDomainRigidity.FiniteTransfer.MixedModelExhaustion` and `OAI.CircleDomainRigidity.FiniteTransfer.RealModelExhaustion` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.UnitDiskCrosscutSeparation`, `OAI.CircleDomainRigidity.UnorientedFiniteCircleGreenFormula`, `OAI.CircleDomainRigidity.instBorelSpaceSphere_35` and `OAI.CircleDomainRigidity.FiniteTransfer.markedNeighborhoods` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.CoordinateExclusionTest`, `OAI.CircleDomainRigidity.GradedRealTest`, `OAI.CircleDomainRigidity.RealCoordinatePresentation`, `OAI.CircleDomainRigidity.SelectableMaskedCoordinate`, `OAI.CircleDomainRigidity.CoordinateExclusionTest.neighborhood`, `OAI.CircleDomainRigidity.CoordinateExclusionTest.presentation`, `OAI.CircleDomainRigidity.UngatedRealTest` and `OAI.CircleDomainRigidity.FiniteTransfer.MaskedCoordinateData.restrictMarks` (definitions bundle `Q146C007` of this split); `OAI.CircleDomainRigidity.SelectedMixedModels`, `OAI.CircleDomainRigidity.SmoothRegularJordanCollars`, `OAI.CircleDomainRigidity.orderedSelectedCoordinates`, `OAI.CircleDomainRigidity.orderedSelectedPresentations`, `OAI.CircleDomainRigidity.realCoordinatesFromPresentations` and `OAI.CircleDomainRigidity.seededMaskedAllowed` (definitions bundle `Q146C010` of this split); `OAI.CircleDomainRigidity.IsCircleDomain` and `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proofs of `OAI.CircleDomainRigidity.exists_signed_compact_scalar_circle_model` and `OAI.CircleDomainRigidity.koebeCircleDomainConjecture_of_constructed_quotient` of this split import it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Topology/SelectedCircleDomain.lean (declaration OAI.CircleDomainRigidity.selected_limit_isCircleDomain)

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010

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

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_35
theorem selected_limit_isCircleDomain
    (hcoarea : PlanarLipschitzFiberCoarea) (hweighted : WeightedPlanarScalarCoarea)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
    (hdust : base.dust = base.quotientDomainᶜ) (hinftyU : OnePoint.infty ∈ base.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hBimage : base.dust = π '' base.physicalDomainᶜ)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ K : Set Sphere, IsCompact K → LocallyConnectedSpace K →
      HasSimpleArcsInConnectedOpens K)
    (E₀ : Set Sphere) (hE₀ : IsCompact E₀) (hE₀U : E₀ ⊆ base.quotientDomain)
    (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ E₀)
    (B₀ : Set base.dust)
    (seed : ℕ → SelectableMaskedCoordinate base π)
    (seedPresentation : ∀ n, RealCoordinatePresentation base π (seed n).coordinate)
    (S : ℕ → Set (CoordinateExclusionTest hsch base π B₀ (B / 4)))
    (q : ℕ → Option (CoordinateExclusionTest hsch base π B₀ (B / 4)))
    (hpref : ∀ n c, c ∈ S n ↔ ∃ k < n, q k = some c)
    (hcover : ∀ t, seededMaskedAllowed seed CoordinateExclusionTest.coordinate (⋃ n, S n) t →
      t.neighborhood ⊆ ⋃ t ∈ ⋃ n, S n, t.neighborhood)
    (hcompat : let D := orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q
      ∀ (j : ℕ ⊕ₗ ℕ) (n : ℕ) (labels : Fin n → ℕ ⊕ₗ ℕ), (∀ i, labels i < j) →
        (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
            (fun k => (D k).coordinate.graph) labels) = 0)
    (F : SelectedMixedModels hsch base hU hdense π he hBimage
      (orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q)
      (orderedSelectedPresentations seed seedPresentation CoordinateExclusionTest.coordinate
        CoordinateExclusionTest.presentation q) B₀)
    (A : AssignedMixedModelLimit F.model) (hB : B / 4 < F.model.real.radius)
    (hBouter : B ≤ 2 * F.model.real.radius)
    (tests : Set (GradedRealTest base π E₀))
    (hretained : ∀ b ∈ tests, ∃ (i : ℕ), (seedPresentation i).coordinate = b.coordinate)
    (htests : ∀ p ∈ base.dust \ (Subtype.val '' B₀),
      ∀ k, ∃ b ∈ tests, b.grade = k ∧ p ∈ b.region)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C₀ / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (J : Set ℕ) [PolishSpace J] (b : J → Sphere) (c : J → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere J))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (J : Set ℕ) [PolishSpace J] (b : J → Sphere) (c : J → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere J)) :
    IsCircleDomain (extendAtInfinity A.function '' base.physicalDomain) := by
  sorry

end CircleDomainRigidity

end

end OAI
end
