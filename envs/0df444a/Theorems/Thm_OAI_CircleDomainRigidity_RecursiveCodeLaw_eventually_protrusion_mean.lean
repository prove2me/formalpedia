-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_RecursiveCodeLaw_eventually_protrusion_mean
-- name    : OAI.CircleDomainRigidity.RecursiveCodeLaw.eventually_protrusion_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:32:43.045723+00:00
-- url     : https://prove2.me/theorems/f2275bbb-4913-427c-b568-6f0cc47790ff
-- title:
--   OAI.CircleDomainRigidity.RecursiveCodeLaw.eventually_protrusion_mean: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.RecursiveCodeLaw.eventually_protrusion_mean` of [lean/OAI/Analysis/CircleDomains/Selection/ProtrusionMeanExclusion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/ProtrusionMeanExclusion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Function Filter MeasureTheory`, `open scoped Topology NNReal ENNReal`, `open FiniteTransfer`):
--
--   ```lean
--    theorem RecursiveCodeLaw.eventually_protrusion_mean
--       (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
--       (hcoarea : PlanarLipschitzFiberCoarea) (hcollar : SmoothRegularJordanCollars)
--       (hselect : BorelPathRelationSelection)
--       (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
--         HasSimpleArcsInConnectedOpens C)
--       {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
--       {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
--       (L : RecursiveCodeLaw base π Flags ω)
--       (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
--       (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
--       (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
--       (hr : ∀ x y, π x = π y ↔ x = y ∨
--         (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
--       (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
--       (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
--       (hp : L.data.target ≠ π OnePoint.infty)
--       {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
--       {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
--       {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
--       (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
--       (s : S) (hqs : π q = σ s)
--       (hseparated : Disjoint (Metric.closedBall T.center (2 * T.radius))
--         (Metric.closedBall (A.center s) (A.radius s)))
--       {R : ℝ} (hR : 0 ≤ R)
--       {g : ℂ → ℝ≥0∞}
--       (D : ℕ → WeightedCollar base.physicalDomain π base.dust L.data.target g)
--       (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
--       (hshrink : ∀ V ∈ 𝓝 L.data.target, ∃ k : ℕ,
--         ∀ n ≥ k, closure (D n).region ⊆ V)
--       (hanchor : Disjoint base.anchor (closure (D 0).region))
--       (hfinite : OnePoint.infty ∉ closure (D 0).region)
--       (hcontours : ∀ n, L.data.gateContours n = frontier (D n).region)
--       (hgates : ∀ n, L.data.gateSets n = Subtype.val ''
--         ((quotientNormalizedMap base.domainEquiv A.function) ⁻¹' closure T.openGate)) :
--       ∃ (δ : ℝ), 0 < δ ∧
--         ∃ (F₀ : ℂ → ℂ) (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)),
--           EqOn F₀ A.function (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain) ∧
--           ∃ B : ℝ≥0, ∀ᶠ n in atTop,
--             ∃ J : ℂ ≃ₜ ℂ, (D n).region = ((↑) : ℂ → Sphere) '' jordanInterior J ∧
--             ∃ Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J)
--               (meanBudgetTolerance B R (δ / 4)),
--               Nonempty (RecursiveMeanOutput hsch Q F₀ hF₀ (A.center s)
--                 ⟨A.radius s, (A.bounds s).2.1⟩ R (δ / 4))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.PathCodeData`, `OAI.CircleDomainRigidity.PathTime`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.jordanInterior` and `OAI.CircleDomainRigidity.sphereMetric` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.HasSimpleArcsInConnectedOpens`, `OAI.CircleDomainRigidity.PlanarLipschitzFiberCoarea`, `OAI.CircleDomainRigidity.TupleType` and `OAI.CircleDomainRigidity.meanBudgetTolerance` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.BorelPathRelationSelection`, `OAI.CircleDomainRigidity.CompactRecursiveReduction`, `OAI.CircleDomainRigidity.RecursiveCodeLaw`, `OAI.CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit`, `OAI.CircleDomainRigidity.FiniteTransfer.CountableRealCoordinates`, `OAI.CircleDomainRigidity.FiniteTransfer.RealModelExhaustion`, `OAI.CircleDomainRigidity.FiniteTransfer.RealTargetEnd` and `OAI.CircleDomainRigidity.RecursiveCodeLaw.data` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.UnitDiskCrosscutSeparation` and `OAI.CircleDomainRigidity.quotientNormalizedMap` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry` and `OAI.CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry.openGate` (definitions bundle `Q146C007` of this split); `OAI.CircleDomainRigidity.WeightedCollar` and `OAI.CircleDomainRigidity.WeightedCollar.region` (definitions bundle `Q146C008` of this split); `OAI.CircleDomainRigidity.RecursiveMeanOutput` and `OAI.CircleDomainRigidity.SmoothRegularJordanCollars` (definitions bundle `Q146C010` of this split); `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.RecursiveCodeLaw.exists_selectable_protrusion_mean` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Selection/ProtrusionMeanExclusion.lean (declaration OAI.CircleDomainRigidity.RecursiveCodeLaw.eventually_protrusion_mean)

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

 theorem RecursiveCodeLaw.eventually_protrusion_mean
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea) (hcollar : SmoothRegularJordanCollars)
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    (L : RecursiveCodeLaw base π Flags ω)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (hp : L.data.target ≠ π OnePoint.infty)
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
    (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
    (s : S) (hqs : π q = σ s)
    (hseparated : Disjoint (Metric.closedBall T.center (2 * T.radius))
      (Metric.closedBall (A.center s) (A.radius s)))
    {R : ℝ} (hR : 0 ≤ R)
    {g : ℂ → ℝ≥0∞}
    (D : ℕ → WeightedCollar base.physicalDomain π base.dust L.data.target g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 L.data.target, ∃ k : ℕ,
      ∀ n ≥ k, closure (D n).region ⊆ V)
    (hanchor : Disjoint base.anchor (closure (D 0).region))
    (hfinite : OnePoint.infty ∉ closure (D 0).region)
    (hcontours : ∀ n, L.data.gateContours n = frontier (D n).region)
    (hgates : ∀ n, L.data.gateSets n = Subtype.val ''
      ((quotientNormalizedMap base.domainEquiv A.function) ⁻¹' closure T.openGate)) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ (F₀ : ℂ → ℂ) (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)),
        EqOn F₀ A.function (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain) ∧
        ∃ B : ℝ≥0, ∀ᶠ n in atTop,
          ∃ J : ℂ ≃ₜ ℂ, (D n).region = ((↑) : ℂ → Sphere) '' jordanInterior J ∧
          ∃ Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J)
            (meanBudgetTolerance B R (δ / 4)),
            Nonempty (RecursiveMeanOutput hsch Q F₀ hF₀ (A.center s)
              ⟨A.radius s, (A.bounds s).2.1⟩ R (δ / 4)) := by
  sorry

end CircleDomainRigidity

end

end OAI
end
