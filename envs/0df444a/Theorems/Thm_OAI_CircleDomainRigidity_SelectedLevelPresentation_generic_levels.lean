-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_SelectedLevelPresentation_generic_levels
-- name    : OAI.CircleDomainRigidity.SelectedLevelPresentation.generic_levels
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:24:44.659275+00:00
-- url     : https://prove2.me/theorems/7bdd5b5c-e38f-4bac-8edb-6bee0db572a1
-- title:
--   OAI.CircleDomainRigidity.SelectedLevelPresentation.generic_levels: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.SelectedLevelPresentation.generic_levels` of [lean/OAI/Analysis/CircleDomains/Selection/SelectedLevelPresentation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/SelectedLevelPresentation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Function Filter MeasureTheory`, `open scoped Topology ENNReal`, `open FiniteTransfer`):
--
--   ```lean
--   theorem SelectedLevelPresentation.generic_levels
--       {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
--       (hcoarea : PlanarLipschitzFiberCoarea)
--       (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
--       (d : PathCodeData Sphere Sphere)
--       (hG : IsOpen d.physicalDomain) (hU : IsOpen d.quotientDomain)
--       (hdense : Dense d.quotientDomain) (hdust : d.dust = d.quotientDomainᶜ)
--       (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
--       (hr : ∀ x y, π x = π y ↔ x = y ∨
--         (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
--       (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
--       (hTD : IsTotallyDisconnected d.quotientDomainᶜ)
--       (hbad : ∀ p ∈ d.physicalDomainᶜ, π p ∈ d.quotientDomainᶜ)
--       (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ d.quotientDomainᶜ)
--       (P : ProbabilityMeasure (BasePathCode d))
--       (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
--       (hocc : meanCodeOccupation d P = sphericalArea.withDensity ρ)
--       (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
--       (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
--       (hweight : countingSquareNorm (fun x : support (d.levelWeights i) => d.levelWeights i x.val) < ∞)
--       (hvisits : countingSquareNorm
--         (fun x : support (d.levelWeights i) => meanVisitCount (codePathLaw d P) x.val) < ∞)
--       (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
--       (hdeleteCover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
--       (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
--       (hH : ∀ j, IsClosed (d.levels j))
--       (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
--       (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
--         (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
--       (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
--       (hτ : meanCodeTuple d P ≪ tupleReference ω)
--       (hsep : UnitDiskCrosscutSeparation)
--       (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
--         (fun x : d.dust => x.val))
--       (R : SelectedLevelPresentation hsch d π C)
--       (hlevel : d.levels i = Prod.swap ⁻¹' C.graph)
--       (hweights : d.levelWeights i = C.dustWeight)
--       (hsingular : (C.singular : Sphere) ∈ Flags) :
--       ∀ᵐ θ : UnitAddCircle ∂volume,
--         (∫⁻ Γ : BasePathCode d, pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1
--           ∂(P : Measure _)) < ∞ ∧
--         ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
--           ¬ ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.PathCodeData`, `OAI.CircleDomainRigidity.PathTime`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.SmoothPlanarSard`, `OAI.CircleDomainRigidity.TagSlot`, `OAI.CircleDomainRigidity.TaggedPath`, `OAI.CircleDomainRigidity.sphereBorel` and `OAI.CircleDomainRigidity.sphereMetric` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.LevelTuple`, `OAI.CircleDomainRigidity.PlanarLipschitzFiberCoarea`, `OAI.CircleDomainRigidity.RankedLevelNullCompatibility`, `OAI.CircleDomainRigidity.TupleType`, `OAI.CircleDomainRigidity.countingSquareNorm`, `OAI.CircleDomainRigidity.instMeasurableSpaceLevelTuple` and `OAI.CircleDomainRigidity.tupleReference` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.BasePathCode`, `OAI.CircleDomainRigidity.EndpointCode`, `OAI.CircleDomainRigidity.codePathLaw`, `OAI.CircleDomainRigidity.instMeasurableSpaceTagSlot`, `OAI.CircleDomainRigidity.meanCodeOccupation`, `OAI.CircleDomainRigidity.meanCodeTuple`, `OAI.CircleDomainRigidity.sphericalArea`, `OAI.CircleDomainRigidity.FiniteTransfer.MaskedCoordinateData` and `OAI.CircleDomainRigidity.FiniteTransfer.MaskedCoordinateData.dustWeight` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.UnitDiskCrosscutSeparation`, `OAI.CircleDomainRigidity.instBorelSpaceSphere_24` and `OAI.CircleDomainRigidity.pathImageCount` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.SelectedLevelPresentation` (definitions bundle `Q146C007` of this split); `OAI.CircleDomainRigidity.meanVisitCount` (definitions bundle `Q146C008` of this split); `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.RecursiveCodeLaw.exists_selectable_protrusion_mean` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/SelectedLevelPresentation.lean (declaration OAI.CircleDomainRigidity.SelectedLevelPresentation.generic_levels)

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C007
import Definitions.Def_Q146C008

section

attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

variable [BorelSpace C(PathTime, Sphere)]

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_24
theorem SelectedLevelPresentation.generic_levels
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere)
    (hG : IsOpen d.physicalDomain) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hdust : d.dust = d.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hTD : IsTotallyDisconnected d.quotientDomainᶜ)
    (hbad : ∀ p ∈ d.physicalDomainᶜ, π p ∈ d.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ d.quotientDomainᶜ)
    (P : ProbabilityMeasure (BasePathCode d))
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) => d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support (d.levelWeights i) => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hdeleteCover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (hsep : UnitDiskCrosscutSeparation)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (R : SelectedLevelPresentation hsch d π C)
    (hlevel : d.levels i = Prod.swap ⁻¹' C.graph)
    (hweights : d.levelWeights i = C.dustWeight)
    (hsingular : (C.singular : Sphere) ∈ Flags) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ Γ : BasePathCode d, pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1
        ∂(P : Measure _)) < ∞ ∧
      ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        ¬ ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
  sorry

end CircleDomainRigidity

end

end OAI
end
