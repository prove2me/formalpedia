-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_exists_ordered_protrusion_test
-- name    : OAI.CircleDomainRigidity.exists_ordered_protrusion_test
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:37:22.756559+00:00
-- url     : https://prove2.me/theorems/016dd060-40a1-4a03-9f4f-09753e842343
-- title:
--   OAI.CircleDomainRigidity.exists_ordered_protrusion_test: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.exists_ordered_protrusion_test` of [lean/OAI/Analysis/CircleDomains/Selection/OrderedProtrusionAvailability.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/OrderedProtrusionAvailability.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Function Filter MeasureTheory`, `open scoped Topology NNReal ENNReal`, `open FiniteTransfer`):
--
--   ```lean
--   theorem exists_ordered_protrusion_test
--       (hcoarea : PlanarLipschitzFiberCoarea) (hweighted : WeightedPlanarScalarCoarea)
--       (hLusin : FiniteTorusAnalyticMeasurability)
--       (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
--       (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
--       (harea : ExteriorCoefficientAreaTheorem)
--       (base : PathCodeData Sphere Sphere)
--       (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
--       (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
--       (hdust : base.dust = base.quotientDomainᶜ)
--       (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
--       (hr : ∀ x y, π x = π y ↔ x = y ∨
--         (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
--       (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
--       (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
--       (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
--       (hinf : OnePoint.infty ∈ base.physicalDomain)
--       (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
--       (harcs : ∀ K : Set Sphere, IsCompact K → LocallyConnectedSpace K →
--         HasSimpleArcsInConnectedOpens K)
--       {I : Type*} [LinearOrder I] [Countable I] (rank : ℕ ≃ I)
--       (D : I → SelectableMaskedCoordinate base π)
--       (pres : ∀ i, SelectedLevelPresentation hsch base π (D i).coordinate)
--       (hcompat : ∀ (j : I) (n : ℕ) (labels : Fin n → I), (∀ i, labels i < j) →
--         (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
--           (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
--             (fun k => (D k).coordinate.graph) labels) = 0)
--       (E₀ : Set Sphere) (hE₀ : IsCompact E₀) (hE₀U : E₀ ⊆ base.quotientDomain)
--       (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ E₀)
--       (B₀ : Set base.dust) (p : B₀) (hpfinite : p.val.val ≠ OnePoint.infty)
--       {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
--       {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
--       {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
--       (hq : q ∈ base.physicalDomainᶜ) (s : S) (hqs : π q = σ s) (hp : p.val.val = σ s)
--       (hne : E.plane ≠ Metric.closedBall (A.center s) (A.radius s))
--       (hB : B / 4 < M.radius)
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
--       ∃ T : CoordinateExclusionTest hsch base π B₀ (B / 4),
--         T.mark = p ∧ T.coordinate.CompatibleWith (range D) ∧
--         (p, (finiteSourceMap A.function (A.plane_open_embedding hG).1,
--           A.center s, (⟨A.radius s, (A.bounds s).2.1⟩ : ℝ≥0)), M.radius) ∈ T.neighborhood
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.PathCodeData`, `OAI.CircleDomainRigidity.PathTime`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.SmoothPlanarSard`, `OAI.CircleDomainRigidity.TagSlot`, `OAI.CircleDomainRigidity.TaggedPath`, `OAI.CircleDomainRigidity.residualImage`, `OAI.CircleDomainRigidity.roundSphereEquiv`, `OAI.CircleDomainRigidity.sphereBorel` and `OAI.CircleDomainRigidity.sphereMetric` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.ExteriorCoefficientAreaTheorem`, `OAI.CircleDomainRigidity.FiniteTorusAnalyticMeasurability`, `OAI.CircleDomainRigidity.HasSimpleArcsInConnectedOpens`, `OAI.CircleDomainRigidity.LevelTuple`, `OAI.CircleDomainRigidity.MeasureImageDuality`, `OAI.CircleDomainRigidity.MeasurePlanLifting`, `OAI.CircleDomainRigidity.PathCostSpace`, `OAI.CircleDomainRigidity.PlanarLipschitzFiberCoarea`, `OAI.CircleDomainRigidity.PolishProbabilityLaws`, `OAI.CircleDomainRigidity.StandardBorelProbabilityLaws`, `OAI.CircleDomainRigidity.TupleType`, `OAI.CircleDomainRigidity.WeightedPlanarScalarCoarea`, `OAI.CircleDomainRigidity.freeComponentFailure`, `OAI.CircleDomainRigidity.instBorelSpacePathCostSpace`, `OAI.CircleDomainRigidity.instMeasurableSpaceLevelTuple`, `OAI.CircleDomainRigidity.instMeasurableSpacePathCostSpaceOfTopologicalSpace`, `OAI.CircleDomainRigidity.instPolishSpacePathCostSpace`, `OAI.CircleDomainRigidity.instTopologicalSpacePathCostSpace` and `OAI.CircleDomainRigidity.tupleReference` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.BasePathCode`, `OAI.CircleDomainRigidity.BorelPathRelationSelection`, `OAI.CircleDomainRigidity.ConstrainedCostCode`, `OAI.CircleDomainRigidity.EndpointCode`, `OAI.CircleDomainRigidity.FiniteCostCode`, `OAI.CircleDomainRigidity.FiniteSource`, `OAI.CircleDomainRigidity.MapDiskData`, `OAI.CircleDomainRigidity.finiteSourceMap`, `OAI.CircleDomainRigidity.instMeasurableSpaceTagSlot`, `OAI.CircleDomainRigidity.pathCostMeasure`, `OAI.CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit`, `OAI.CircleDomainRigidity.FiniteTransfer.CountableRealCoordinates`, `OAI.CircleDomainRigidity.FiniteTransfer.RealModelExhaustion`, `OAI.CircleDomainRigidity.FiniteTransfer.RealTargetEnd`, `OAI.CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit.plane_open_embedding`, `OAI.CircleDomainRigidity.FiniteTransfer.MaskedCoordinateData` and `OAI.CircleDomainRigidity.FiniteTransfer.RealTargetEnd.plane` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.UnitDiskCrosscutSeparation` and `OAI.CircleDomainRigidity.instBorelSpaceSphere_33` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.CoordinateExclusionTest`, `OAI.CircleDomainRigidity.SelectableMaskedCoordinate`, `OAI.CircleDomainRigidity.SelectedLevelPresentation` and `OAI.CircleDomainRigidity.CoordinateExclusionTest.neighborhood` (definitions bundle `Q146C007` of this split); `OAI.CircleDomainRigidity.SmoothRegularJordanCollars` and `OAI.CircleDomainRigidity.SelectableMaskedCoordinate.CompatibleWith` (definitions bundle `Q146C010` of this split); `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.selected_limit_isCircleDomain` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/OrderedProtrusionAvailability.lean (declaration OAI.CircleDomainRigidity.exists_ordered_protrusion_test)

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

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_33
theorem exists_ordered_protrusion_test
    (hcoarea : PlanarLipschitzFiberCoarea) (hweighted : WeightedPlanarScalarCoarea)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (harea : ExteriorCoefficientAreaTheorem)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
    (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ K : Set Sphere, IsCompact K → LocallyConnectedSpace K →
      HasSimpleArcsInConnectedOpens K)
    {I : Type*} [LinearOrder I] [Countable I] (rank : ℕ ≃ I)
    (D : I → SelectableMaskedCoordinate base π)
    (pres : ∀ i, SelectedLevelPresentation hsch base π (D i).coordinate)
    (hcompat : ∀ (j : I) (n : ℕ) (labels : Fin n → I), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
          (fun k => (D k).coordinate.graph) labels) = 0)
    (E₀ : Set Sphere) (hE₀ : IsCompact E₀) (hE₀U : E₀ ⊆ base.quotientDomain)
    (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ E₀)
    (B₀ : Set base.dust) (p : B₀) (hpfinite : p.val.val ≠ OnePoint.infty)
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
    (hq : q ∈ base.physicalDomainᶜ) (s : S) (hqs : π q = σ s) (hp : p.val.val = σ s)
    (hne : E.plane ≠ Metric.closedBall (A.center s) (A.radius s))
    (hB : B / 4 < M.radius)
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
    ∃ T : CoordinateExclusionTest hsch base π B₀ (B / 4),
      T.mark = p ∧ T.coordinate.CompatibleWith (range D) ∧
      (p, (finiteSourceMap A.function (A.plane_open_embedding hG).1,
        A.center s, (⟨A.radius s, (A.bounds s).2.1⟩ : ℝ≥0)), M.radius) ∈ T.neighborhood := by
  sorry

end CircleDomainRigidity

end

end OAI
end
