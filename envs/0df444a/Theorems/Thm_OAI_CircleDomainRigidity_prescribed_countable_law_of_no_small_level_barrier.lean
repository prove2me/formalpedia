-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_prescribed_countable_law_of_no_small_level_barrier
-- name    : OAI.CircleDomainRigidity.prescribed_countable_law_of_no_small_level_barrier
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:27:05.297581+00:00
-- url     : https://prove2.me/theorems/ed382128-109a-44f3-baed-dde1284d340e
-- title:
--   OAI.CircleDomainRigidity.prescribed_countable_law_of_no_small_level_barrier: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.prescribed_countable_law_of_no_small_level_barrier` of [lean/OAI/Analysis/CircleDomains/Probability/PriorBarrierCodeLaw.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Probability/PriorBarrierCodeLaw.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Function Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`):
--
--   ```lean
--   theorem prescribed_countable_law_of_no_small_level_barrier
--       (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability) (hsard : SmoothPlanarSard)
--       (hsch : PlanarSchoenflies)
--       (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
--       (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
--       (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
--       (hr : ∀x y, π x = π y ↔ x = y ∨
--         (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
--       (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
--       (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
--       (hBU : d.dustᶜ ⊆ d.quotientDomain)
--       (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ d.dust)
--       (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
--       (ν : Measure Sphere) [IsFiniteMeasure ν] [NullSingletonClass ν]
--       (hinf : OnePoint.infty ∈ d.physicalDomain)
--       (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
--       (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
--       (hinfE : π OnePoint.infty ∈ interior d.anchor)
--       (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
--       {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π d.dust p g₀)
--       (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
--       (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
--       (hED : Disjoint d.anchor (closure (D 0).region))
--       (f : d.quotientDomain → Sphere) (hf : Continuous f)
--       (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
--       (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
--       (harcs : ∀C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
--         HasSimpleArcsInConnectedOpens C)
--       (previous : PriorLevelFamily d.physicalDomain π)
--       (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
--         previous.graph i)
--       (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
--       (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
--       (flags : Set Sphere) (hflags : flags.Countable)
--       (C : ℝ) (hC : 0 ≤ C)
--       (hderiv : ∀z : ℂ,
--         ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
--           C / (1 + ‖z‖ ^ 2))
--       (htarget : d.target = p)
--       (hcontours : d.gateContours = fun j => frontier (D j).region)
--       (hgates : d.gateSets = fun _ => Subtype.val '' (f ⁻¹' closure W₂))
--       {A : Type*} [TopologicalSpace A] [Countable A] [MeasurableSpace A] [BorelSpace A]
--       (a : A → Sphere) (ha : Injective a) (haB : range a ⊆ d.dust)
--       (c : A → ℝ≥0∞) (hc : (∑'s, c s ^ 2) < ∞)
--       (ω : TupleType → ℝ≥0∞) (hω : ∀i, ω i ≠ 0)
--       [PolishSpace A] [StandardBorelSpace (ConstrainedCostCode d a c ν)]
--       (β : ℝ≥0∞)
--       (hno : ∀R : CompatibleLevelBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
--         β ≤ R.controlledSize)
--       (hωsum : (∑'i, ω i) < ∞)
--       (hdual : MeasureImageDuality (ConstrainedCostCode d a c ν) (PathCostSpace Sphere A))
--       (hlift : MeasurePlanLifting (ConstrainedCostCode d a c ν) (PathCostSpace Sphere A))
--       (r : ℝ≥0) (hrpos : 0 < r)
--       (hrbound : (r : ℝ≥0∞) < (β / (2 * barrierConstructionConstant C)) ^ 2)
--       (hc0 : ∀s, c s ≠ 0) (hct : ∀s, c s ≠ ∞)
--       (hν : ν d.dustᶜ = 0)
--       (hunique : ∀x ∈ d.dust \ flags, ∀i t u,
--         (t, x) ∈ d.levels i → (u, x) ∈ d.levels i → t = u) :
--       ∃(P : ProbabilityMeasure (BasePathCode d)) (g : Sphere → ℝ≥0∞) (q : LevelTuple → ℝ≥0∞),
--         Measurable g ∧ Measurable q ∧
--         meanCodeOccupation d P = sphericalArea.withDensity g ∧
--         (∫⁻y, g y ^ 2 ∂sphericalArea) ≤ (r : ℝ≥0∞)⁻¹ ∧
--         countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤
--           (r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1 ∧
--         meanCodeTuple d P = (tupleReference ω).withDensity q ∧
--         (∫⁻t, q t ^ 2 ∂tupleReference ω) ≤ (r : ℝ≥0∞)⁻¹ ∧
--         (∀k, slotLaw d P k ≪ tupleReference ω) ∧
--         (∫⁻x, pathHitProbability (codePathLaw d P) x ∂ν) = 0 ∧
--         (∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.PathCodeData`, `OAI.CircleDomainRigidity.PathTime`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.SmoothPlanarSard`, `OAI.CircleDomainRigidity.TagSlot`, `OAI.CircleDomainRigidity.TaggedPath`, `OAI.CircleDomainRigidity.residualImage`, `OAI.CircleDomainRigidity.roundSphereEquiv`, `OAI.CircleDomainRigidity.sphereBorel` and `OAI.CircleDomainRigidity.sphereMetric` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.FiniteTorusAnalyticMeasurability`, `OAI.CircleDomainRigidity.HasSimpleArcsInConnectedOpens`, `OAI.CircleDomainRigidity.LevelTuple`, `OAI.CircleDomainRigidity.MeasureImageDuality`, `OAI.CircleDomainRigidity.MeasurePlanLifting`, `OAI.CircleDomainRigidity.PathCostSpace`, `OAI.CircleDomainRigidity.TupleType`, `OAI.CircleDomainRigidity.WeightedPlanarScalarCoarea`, `OAI.CircleDomainRigidity.barrierConstructionConstant`, `OAI.CircleDomainRigidity.countingSquareNorm`, `OAI.CircleDomainRigidity.instBorelSpacePathCostSpace`, `OAI.CircleDomainRigidity.instMeasurableSpaceLevelTuple`, `OAI.CircleDomainRigidity.instMeasurableSpacePathCostSpaceOfTopologicalSpace`, `OAI.CircleDomainRigidity.instPolishSpacePathCostSpace`, `OAI.CircleDomainRigidity.instTopologicalSpacePathCostSpace` and `OAI.CircleDomainRigidity.tupleReference` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.BasePathCode`, `OAI.CircleDomainRigidity.ConstrainedCostCode`, `OAI.CircleDomainRigidity.EndpointCode`, `OAI.CircleDomainRigidity.FiniteCostCode`, `OAI.CircleDomainRigidity.PriorLevelFamily`, `OAI.CircleDomainRigidity.codePathLaw`, `OAI.CircleDomainRigidity.instMeasurableSpaceTagSlot`, `OAI.CircleDomainRigidity.meanCodeOccupation`, `OAI.CircleDomainRigidity.meanCodeTuple`, `OAI.CircleDomainRigidity.pathCostMeasure`, `OAI.CircleDomainRigidity.pathHitProbability` and `OAI.CircleDomainRigidity.sphericalArea` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.instBorelSpaceSphere_27` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.CompatibleLevelBarrier` and `OAI.CircleDomainRigidity.CompatibleLevelBarrier.controlledSize` (definitions bundle `Q146C007` of this split); `OAI.CircleDomainRigidity.WeightedCollar`, `OAI.CircleDomainRigidity.meanVisitCount`, `OAI.CircleDomainRigidity.slotLaw` and `OAI.CircleDomainRigidity.WeightedCollar.region` (definitions bundle `Q146C008` of this split); `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.exists_ordered_protrusion_test` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Probability/PriorBarrierCodeLaw.lean (declaration OAI.CircleDomainRigidity.prescribed_countable_law_of_no_small_level_barrier)

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C007
import Definitions.Def_Q146C008

section

attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_rf75f61_1 : BorelSpace Sphere := ⟨rfl⟩
theorem prescribed_countable_law_of_no_small_level_barrier
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (ν : Measure Sphere) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π d.dust p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint d.anchor (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : PriorLevelFamily d.physicalDomain π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      previous.graph i)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (flags : Set Sphere) (hflags : flags.Countable)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (htarget : d.target = p)
    (hcontours : d.gateContours = fun j => frontier (D j).region)
    (hgates : d.gateSets = fun _ => Subtype.val '' (f ⁻¹' closure W₂))
    {A : Type*} [TopologicalSpace A] [Countable A] [MeasurableSpace A] [BorelSpace A]
    (a : A → Sphere) (ha : Injective a) (haB : range a ⊆ d.dust)
    (c : A → ℝ≥0∞) (hc : (∑'s, c s ^ 2) < ∞)
    (ω : TupleType → ℝ≥0∞) (hω : ∀i, ω i ≠ 0)
    [PolishSpace A] [StandardBorelSpace (ConstrainedCostCode d a c ν)]
    (β : ℝ≥0∞)
    (hno : ∀R : CompatibleLevelBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
      β ≤ R.controlledSize)
    (hωsum : (∑'i, ω i) < ∞)
    (hdual : MeasureImageDuality (ConstrainedCostCode d a c ν) (PathCostSpace Sphere A))
    (hlift : MeasurePlanLifting (ConstrainedCostCode d a c ν) (PathCostSpace Sphere A))
    (r : ℝ≥0) (hrpos : 0 < r)
    (hrbound : (r : ℝ≥0∞) < (β / (2 * barrierConstructionConstant C)) ^ 2)
    (hc0 : ∀s, c s ≠ 0) (hct : ∀s, c s ≠ ∞)
    (hν : ν d.dustᶜ = 0)
    (hunique : ∀x ∈ d.dust \ flags, ∀i t u,
      (t, x) ∈ d.levels i → (u, x) ∈ d.levels i → t = u) :
    ∃(P : ProbabilityMeasure (BasePathCode d)) (g : Sphere → ℝ≥0∞) (q : LevelTuple → ℝ≥0∞),
      Measurable g ∧ Measurable q ∧
      meanCodeOccupation d P = sphericalArea.withDensity g ∧
      (∫⁻y, g y ^ 2 ∂sphericalArea) ≤ (r : ℝ≥0∞)⁻¹ ∧
      countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤
        (r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1 ∧
      meanCodeTuple d P = (tupleReference ω).withDensity q ∧
      (∫⁻t, q t ^ 2 ∂tupleReference ω) ≤ (r : ℝ≥0∞)⁻¹ ∧
      (∀k, slotLaw d P k ≪ tupleReference ω) ∧
      (∫⁻x, pathHitProbability (codePathLaw d P) x ∂ν) = 0 ∧
      (∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0) := by
  sorry

end CircleDomainRigidity

end

end OAI
end
