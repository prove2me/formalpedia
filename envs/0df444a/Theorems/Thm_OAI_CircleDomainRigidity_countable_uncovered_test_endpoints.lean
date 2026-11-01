-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_countable_uncovered_test_endpoints
-- name    : OAI.CircleDomainRigidity.countable_uncovered_test_endpoints
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T05:37:32.75469+00:00
-- url     : https://prove2.me/theorems/77e47640-18eb-4824-aaca-aee778320ec0
-- title:
--   OAI.CircleDomainRigidity.countable_uncovered_test_endpoints: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.countable_uncovered_test_endpoints` of [lean/OAI/Analysis/CircleDomains/Selection/CountableUncoveredTestEnds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/CountableUncoveredTestEnds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Function Filter MeasureTheory`, `open scoped ENNReal NNReal Topology`):
--
--   ```lean
--   theorem countable_uncovered_test_endpoints
--       (hcross : UnitDiskAlternatingContinua)
--       (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
--       (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
--       (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
--       (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
--       (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
--       (hr : ∀ x y, π x = π y ↔ x = y ∨
--         (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
--       (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
--       (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
--       (hBU : d.dustᶜ ⊆ d.quotientDomain) (hdense : Dense d.quotientDomain)
--       (hinfty : π OnePoint.infty ∉ d.dust)
--       (hbad : ∀ x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
--       (hinf : OnePoint.infty ∈ d.physicalDomain)
--       (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
--       (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
--       (hinfE : π OnePoint.infty ∈ interior d.anchor)
--       (P : Set Sphere) (hPB : P ⊆ d.dust)
--       {g₀ : ℂ → ℝ≥0∞}
--       (D : ∀ p : P, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
--       (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
--       (hshrink : ∀ p : P, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
--         ∀ n ≥ k, closure (D p n).region ⊆ V)
--       (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
--       (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
--       (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
--         HasSimpleArcsInConnectedOpens C)
--       (A : Set (GradedRealTest d π EStar)) (k : ℕ)
--       (hmiss : ∀ p ∈ P, p ∈ uncoveredTestEnds A k)
--       (hcover : ∀ b, GradedRealTest.Allowed A b → ∀ x ∈ b.toUngatedRealTest.openEnds,
--         ∃ a ∈ A, a.grade = b.grade ∧ x ∈ a.toUngatedRealTest.openEnds)
--       (c : ℕ → UngatedRealTest d π EStar) (M : Set Sphere)
--       (hMc : M.Countable) (hMB : M ⊆ d.dust)
--       (hM : ∀ i, (c i).exclusions ∩ d.dust ⊆ M)
--       (hselected : ∀ a ∈ insert (UngatedRealTest.zeroTest d π EStar)
--         (GradedRealTest.toUngatedRealTest '' A), ∃ i, c i = a)
--       (hcompat : OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M))
--       (C : ℝ) (hC : 0 ≤ C)
--       (hderiv : ∀ z : ℂ,
--         ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
--           C / (1 + ‖z‖ ^ 2))
--       (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
--         StandardBorelProbabilityLaws (BasePathCode e))
--       (hpath : PolishProbabilityLaws C(PathTime, Sphere))
--       (ω : TupleType → ℝ≥0∞) (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
--       (hdual : ∀ (e : PathCodeData Sphere Sphere)
--         (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
--         (ν : Measure Sphere) [IsFiniteMeasure ν]
--         [StandardBorelSpace (ConstrainedCostCode e b c ν)],
--         MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
--       (hlift : ∀ (e : PathCodeData Sphere Sphere)
--         (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
--         (ν : Measure Sphere) [IsFiniteMeasure ν]
--         [StandardBorelSpace (ConstrainedCostCode e b c ν)],
--         MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
--       : P.Countable
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.PathCodeData`, `OAI.CircleDomainRigidity.PathTime`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.SmoothPlanarSard`, `OAI.CircleDomainRigidity.TagSlot`, `OAI.CircleDomainRigidity.TaggedPath`, `OAI.CircleDomainRigidity.residualImage`, `OAI.CircleDomainRigidity.roundSphereEquiv`, `OAI.CircleDomainRigidity.sphereBorel` and `OAI.CircleDomainRigidity.sphereMetric` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.FiniteTorusAnalyticMeasurability`, `OAI.CircleDomainRigidity.HasSimpleArcsInConnectedOpens`, `OAI.CircleDomainRigidity.MeasureImageDuality`, `OAI.CircleDomainRigidity.MeasurePlanLifting`, `OAI.CircleDomainRigidity.OrderedLevelNullCompatibility`, `OAI.CircleDomainRigidity.PathCostSpace`, `OAI.CircleDomainRigidity.PolishProbabilityLaws`, `OAI.CircleDomainRigidity.StandardBorelProbabilityLaws`, `OAI.CircleDomainRigidity.TupleType`, `OAI.CircleDomainRigidity.UnitDiskAlternatingContinua`, `OAI.CircleDomainRigidity.WeightedPlanarScalarCoarea`, `OAI.CircleDomainRigidity.instBorelSpacePathCostSpace`, `OAI.CircleDomainRigidity.instMeasurableSpacePathCostSpaceOfTopologicalSpace`, `OAI.CircleDomainRigidity.instPolishSpacePathCostSpace` and `OAI.CircleDomainRigidity.instTopologicalSpacePathCostSpace` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.BasePathCode`, `OAI.CircleDomainRigidity.ConstrainedCostCode`, `OAI.CircleDomainRigidity.EndpointCode`, `OAI.CircleDomainRigidity.FiniteCostCode`, `OAI.CircleDomainRigidity.instMeasurableSpaceTagSlot` and `OAI.CircleDomainRigidity.pathCostMeasure` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.instBorelSpaceSphere_32` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.GradedRealTest`, `OAI.CircleDomainRigidity.UngatedRealTest`, `OAI.CircleDomainRigidity.GradedRealTest.Allowed` and `OAI.CircleDomainRigidity.UngatedRealTest.zeroTest` (definitions bundle `Q146C007` of this split); `OAI.CircleDomainRigidity.WeightedCollar` and `OAI.CircleDomainRigidity.WeightedCollar.region` (definitions bundle `Q146C008` of this split); `OAI.CircleDomainRigidity.realTestLevelData`, `OAI.CircleDomainRigidity.uncoveredTestEnds` and `OAI.CircleDomainRigidity.UngatedRealTest.openEnds` (definitions bundle `Q146C010` of this split); `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.koebeCircleDomainConjecture_of_constructed_quotient` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/CountableUncoveredTestEnds.lean (declaration OAI.CircleDomainRigidity.countable_uncovered_test_endpoints)

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010

section

attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
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

local instance localInst_r5ec6a1_1 : BorelSpace Sphere := ⟨rfl⟩
theorem countable_uncovered_test_endpoints
    (hcross : UnitDiskAlternatingContinua)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀ x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (P : Set Sphere) (hPB : P ⊆ d.dust)
    {g₀ : ℂ → ℝ≥0∞}
    (D : ∀ p : P, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
    (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
    (hshrink : ∀ p : P, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
      ∀ n ≥ k, closure (D p n).region ⊆ V)
    (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (A : Set (GradedRealTest d π EStar)) (k : ℕ)
    (hmiss : ∀ p ∈ P, p ∈ uncoveredTestEnds A k)
    (hcover : ∀ b, GradedRealTest.Allowed A b → ∀ x ∈ b.toUngatedRealTest.openEnds,
      ∃ a ∈ A, a.grade = b.grade ∧ x ∈ a.toUngatedRealTest.openEnds)
    (c : ℕ → UngatedRealTest d π EStar) (M : Set Sphere)
    (hMc : M.Countable) (hMB : M ⊆ d.dust)
    (hM : ∀ i, (c i).exclusions ∩ d.dust ⊆ M)
    (hselected : ∀ a ∈ insert (UngatedRealTest.zeroTest d π EStar)
      (GradedRealTest.toUngatedRealTest '' A), ∃ i, c i = a)
    (hcompat : OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M))
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    : P.Countable := by
  sorry

end CircleDomainRigidity

end

end OAI
end
