-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_RecursiveCodeLaw_exists_selectable_protrusion_mean
-- name    : OAI.CircleDomainRigidity.RecursiveCodeLaw.exists_selectable_protrusion_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:33:55.708669+00:00
-- url     : https://prove2.me/theorems/6185567c-da30-44c1-a51b-bbe4d6f5526c
-- title:
--   OAI.CircleDomainRigidity.RecursiveCodeLaw.exists_selectable_protrusion_mean: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.RecursiveCodeLaw.exists_selectable_protrusion_mean` of [lean/OAI/Analysis/CircleDomains/Selection/SelectableProtrusionMean.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/SelectableProtrusionMean.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Function Filter MeasureTheory`, `open scoped Topology NNReal ENNReal`, `open FiniteTransfer`):
--
--   ```lean
--   theorem RecursiveCodeLaw.exists_selectable_protrusion_mean
--       {I : Type*} [LinearOrder I] (rank : ℕ → I) (hrank : Injective rank)
--       (hcoarea : PlanarLipschitzFiberCoarea)
--       (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
--       (base : PathCodeData Sphere Sphere)
--       (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
--       (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
--       (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
--       (hr : ∀ x y, π x = π y ↔ x = y ∨
--         (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
--       (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
--       (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
--       (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
--       (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ base.quotientDomainᶜ)
--       (C : ℕ → MaskedCoordinateData base.physicalDomain base.quotientDomain π
--         (fun x : base.dust => x.val))
--       (presentation : ∀ i, SelectedLevelPresentation hsch base π (C i))
--       (hlevel : ∀ i, base.levels i = Prod.swap ⁻¹' (C i).graph)
--       (hweights : ∀ i, base.levelWeights i = (C i).dustWeight)
--       (hmarked : ∀ i, support (base.levelWeights i) ⊆ Flags)
--       (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
--       (hP : RankedLevelNullCompatibility rank base.levels (base.quotientDomainᶜ \ Flags))
--       (hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ j a b,
--         (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
--       (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
--       (L : RecursiveCodeLaw base π Flags ω)
--       (hLusin : FiniteTorusAnalyticMeasurability)
--       (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
--       (harcs : ∀ D : Set Sphere, IsCompact D → LocallyConnectedSpace D →
--         HasSimpleArcsInConnectedOpens D)
--       (previous : PriorLevelFamily base.physicalDomain π)
--       (hprevious : ∀ i, previous.graph i = (C i).graph)
--       (hweighted : WeightedPlanarScalarCoarea) (hcollar : SmoothRegularJordanCollars)
--       (hselect : BorelPathRelationSelection)
--       (Candidates : Set (SelectableMaskedCoordinate base π))
--       (label : SelectableMaskedCoordinate base π → ℕ)
--       (hflags : ∀ c ∈ Candidates, c.flags ⊆ Flags)
--       (hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c))
--       {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
--       {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
--       {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
--       (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
--       (s : S) (hqs : π q = σ s) (htarget : L.data.target = σ s)
--       (hp : L.data.target ≠ π OnePoint.infty)
--       (hseparated : Disjoint (Metric.closedBall T.center (2 * T.radius))
--         (Metric.closedBall (A.center s) (A.radius s)))
--       {g : ℂ → ℝ≥0∞}
--       (D : ℕ → WeightedCollar base.physicalDomain π base.dust L.data.target g)
--       (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
--       (hshrink : ∀ V ∈ 𝓝 L.data.target, ∃ k : ℕ, ∀ n ≥ k, closure (D n).region ⊆ V)
--       (hanchor : Disjoint base.anchor (closure (D 0).region))
--       (hfinite : OnePoint.infty ∉ closure (D 0).region)
--       (hcontours : ∀ n, L.data.gateContours n = frontier (D n).region)
--       (hgates : ∀ n, L.data.gateSets n = Subtype.val ''
--         ((quotientNormalizedMap base.domainEquiv A.function) ⁻¹' closure T.openGate))
--       (B R : ℝ) (hB : B / 4 < M.radius) (hR : 5 * M.radius < R)
--       (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ base.anchor) :
--       ∃ c : SelectableMaskedCoordinate base π, c.CompatibleWith Candidates ∧
--         Nonempty (MeanCoordinatePresentation hsch base π c.coordinate) ∧
--         (c.coordinate.singular : Sphere) = σ s ∧
--         ∃ W : MeanExclusionWitness c.coordinate A.function (A.plane_open_embedding hG).1
--           (A.center s) ⟨A.radius s, (A.bounds s).2.1⟩ R,
--           (∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ < B) ∧
--           ((finiteSourceMap A.function (A.plane_open_embedding hG).1,
--             A.center s, (⟨A.radius s, (A.bounds s).2.1⟩ : ℝ≥0)), M.radius) ∈
--               W.sizedNeighborhood (B / 4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.PathCodeData`, `OAI.CircleDomainRigidity.PathTime`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.SmoothPlanarSard`, `OAI.CircleDomainRigidity.jordanInterior` and `OAI.CircleDomainRigidity.sphereMetric` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.FiniteTorusAnalyticMeasurability`, `OAI.CircleDomainRigidity.HasSimpleArcsInConnectedOpens`, `OAI.CircleDomainRigidity.LevelTuple`, `OAI.CircleDomainRigidity.PlanarLipschitzFiberCoarea`, `OAI.CircleDomainRigidity.RankedLevelNullCompatibility`, `OAI.CircleDomainRigidity.TupleType`, `OAI.CircleDomainRigidity.WeightedPlanarScalarCoarea`, `OAI.CircleDomainRigidity.instMeasurableSpaceLevelTuple` and `OAI.CircleDomainRigidity.tupleReference` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.BorelPathRelationSelection`, `OAI.CircleDomainRigidity.FiniteSource`, `OAI.CircleDomainRigidity.MapDiskData`, `OAI.CircleDomainRigidity.PriorLevelFamily`, `OAI.CircleDomainRigidity.RecursiveCodeLaw`, `OAI.CircleDomainRigidity.finiteSourceMap`, `OAI.CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit`, `OAI.CircleDomainRigidity.FiniteTransfer.CountableRealCoordinates`, `OAI.CircleDomainRigidity.FiniteTransfer.MaskedCoordinateData`, `OAI.CircleDomainRigidity.FiniteTransfer.RealModelExhaustion`, `OAI.CircleDomainRigidity.FiniteTransfer.RealTargetEnd`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.data`, `OAI.CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit.plane_open_embedding` and `OAI.CircleDomainRigidity.FiniteTransfer.MaskedCoordinateData.dustWeight` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.UnitDiskCrosscutSeparation` and `OAI.CircleDomainRigidity.quotientNormalizedMap` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.MeanCoordinatePresentation`, `OAI.CircleDomainRigidity.MeanExclusionWitness`, `OAI.CircleDomainRigidity.SelectableMaskedCoordinate`, `OAI.CircleDomainRigidity.SelectedLevelPresentation`, `OAI.CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry`, `OAI.CircleDomainRigidity.MeanExclusionWitness.sizedNeighborhood` and `OAI.CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry.openGate` (definitions bundle `Q146C007` of this split); `OAI.CircleDomainRigidity.WeightedCollar` and `OAI.CircleDomainRigidity.WeightedCollar.region` (definitions bundle `Q146C008` of this split); `OAI.CircleDomainRigidity.SmoothRegularJordanCollars` and `OAI.CircleDomainRigidity.SelectableMaskedCoordinate.CompatibleWith` (definitions bundle `Q146C010` of this split); `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.exists_ordered_protrusion_test` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/SelectableProtrusionMean.lean (declaration OAI.CircleDomainRigidity.RecursiveCodeLaw.exists_selectable_protrusion_mean)

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

 local instance instBorelSpaceSphere_30_r5428db_1 : BorelSpace Sphere := ⟨rfl⟩
theorem RecursiveCodeLaw.exists_selectable_protrusion_mean
    {I : Type*} [LinearOrder I] (rank : ℕ → I) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ base.quotientDomainᶜ)
    (C : ℕ → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val))
    (presentation : ∀ i, SelectedLevelPresentation hsch base π (C i))
    (hlevel : ∀ i, base.levels i = Prod.swap ⁻¹' (C i).graph)
    (hweights : ∀ i, base.levelWeights i = (C i).dustWeight)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ Flags)
    (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
    (hP : RankedLevelNullCompatibility rank base.levels (base.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (L : RecursiveCodeLaw base π Flags ω)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ D : Set Sphere, IsCompact D → LocallyConnectedSpace D →
      HasSimpleArcsInConnectedOpens D)
    (previous : PriorLevelFamily base.physicalDomain π)
    (hprevious : ∀ i, previous.graph i = (C i).graph)
    (hweighted : WeightedPlanarScalarCoarea) (hcollar : SmoothRegularJordanCollars)
    (hselect : BorelPathRelationSelection)
    (Candidates : Set (SelectableMaskedCoordinate base π))
    (label : SelectableMaskedCoordinate base π → ℕ)
    (hflags : ∀ c ∈ Candidates, c.flags ⊆ Flags)
    (hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c))
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
    (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
    (s : S) (hqs : π q = σ s) (htarget : L.data.target = σ s)
    (hp : L.data.target ≠ π OnePoint.infty)
    (hseparated : Disjoint (Metric.closedBall T.center (2 * T.radius))
      (Metric.closedBall (A.center s) (A.radius s)))
    {g : ℂ → ℝ≥0∞}
    (D : ℕ → WeightedCollar base.physicalDomain π base.dust L.data.target g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 L.data.target, ∃ k : ℕ, ∀ n ≥ k, closure (D n).region ⊆ V)
    (hanchor : Disjoint base.anchor (closure (D 0).region))
    (hfinite : OnePoint.infty ∉ closure (D 0).region)
    (hcontours : ∀ n, L.data.gateContours n = frontier (D n).region)
    (hgates : ∀ n, L.data.gateSets n = Subtype.val ''
      ((quotientNormalizedMap base.domainEquiv A.function) ⁻¹' closure T.openGate))
    (B R : ℝ) (hB : B / 4 < M.radius) (hR : 5 * M.radius < R)
    (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ base.anchor) :
    ∃ c : SelectableMaskedCoordinate base π, c.CompatibleWith Candidates ∧
      Nonempty (MeanCoordinatePresentation hsch base π c.coordinate) ∧
      (c.coordinate.singular : Sphere) = σ s ∧
      ∃ W : MeanExclusionWitness c.coordinate A.function (A.plane_open_embedding hG).1
        (A.center s) ⟨A.radius s, (A.bounds s).2.1⟩ R,
        (∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ < B) ∧
        ((finiteSourceMap A.function (A.plane_open_embedding hG).1,
          A.center s, (⟨A.radius s, (A.bounds s).2.1⟩ : ℝ≥0)), M.radius) ∈
            W.sizedNeighborhood (B / 4) := by
  sorry

end CircleDomainRigidity

end

end OAI
end
