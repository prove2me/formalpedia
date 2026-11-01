-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_exists_filled_first_arrival_barrier_potential
-- name    : OAI.CircleDomainRigidity.exists_filled_first_arrival_barrier_potential
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:25:12.458173+00:00
-- url     : https://prove2.me/theorems/355c13e0-2e2c-4126-8bbb-71842da9a9b0
-- title:
--   OAI.CircleDomainRigidity.exists_filled_first_arrival_barrier_potential: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.exists_filled_first_arrival_barrier_potential` of [lean/OAI/Analysis/CircleDomains/Modulus/FilledFirstArrivalBarrier.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Modulus/FilledFirstArrivalBarrier.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Function Filter MeasureTheory`, `open scoped ENNReal Topology`):
--
--   ```lean
--   theorem exists_filled_first_arrival_barrier_potential
--       (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
--       (hsch : PlanarSchoenflies)
--       (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
--       (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
--       (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
--       (hr : ∀x y, π x = π y ↔ x = y ∨
--         (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
--       (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
--       {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
--       (hUB : Disjoint d.quotientDomain B) (hBU : Bᶜ ⊆ d.quotientDomain)
--       (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ B)
--       (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
--       (ν : Measure Sphere) [NullSingletonClass ν]
--       (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
--       (E : Set Sphere) (hE : IsClosed E) (hEU : E ⊆ d.quotientDomain)
--       (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
--       {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π B p g₀)
--       (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
--       (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
--       (hED : Disjoint E (closure (D 0).region))
--       (f : d.quotientDomain → Sphere) (hf : Continuous f)
--       (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
--       (g : Sphere → ℝ≥0∞) (hg : Measurable g)
--       (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
--       (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
--       (hm₂ : (∑' x, m x ^ 2) ≠ ∞)
--       (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
--       (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
--       (hunit : ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
--         AllowedTaggedPath d ν N (ρ.val, θ) → ρ.val ⊥ ∈ E → ρ.val ⊤ = p →
--         (∀t < (⊤ : PathTime), ρ.val t ≠ p) →
--         GateRules (fun j => frontier (D j).region)
--           (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) ρ.val →
--         1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
--           preterminalToll ρ.val m) :
--       ∃k : ℕ, ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞, ∃u : Sphere → ℝ,
--         IsOpen O ∧ closure O ⊆ d.quotientDomain ∧ Disjoint E (closure O) ∧
--         (∀x : d.quotientDomain, x.val ∈ closure O → f x ∉ W₁) ∧
--         Measurable g₁ ∧ (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
--         (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
--         (∀x, u x ∈ Icc 0 1) ∧ (∀x ∈ E, u x = 0) ∧
--         (∀x ∈ closure (D k).region, u x = 1) ∧
--         (∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
--           Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
--           ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g₁ m Γ.1) ∧
--         ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
--           liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.AllowedTaggedPath`, `OAI.CircleDomainRigidity.PathCodeData`, `OAI.CircleDomainRigidity.PathTime`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.SmoothPlanarSard`, `OAI.CircleDomainRigidity.TagSlot`, `OAI.CircleDomainRigidity.physicalDomainLength`, `OAI.CircleDomainRigidity.sphereBorel` and `OAI.CircleDomainRigidity.sphereMetric` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.WeightedPlanarScalarCoarea` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.FinitePhysicalPath`, `OAI.CircleDomainRigidity.GateRules`, `OAI.CircleDomainRigidity.TaggedPhysicalPath`, `OAI.CircleDomainRigidity.dyadicPhysicalOccupation`, `OAI.CircleDomainRigidity.physicalTollCost` and `OAI.CircleDomainRigidity.sphericalArea` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.instBorelSpaceSphere_21` and `OAI.CircleDomainRigidity.preterminalToll` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.WeightedCollar` and `OAI.CircleDomainRigidity.WeightedCollar.region` (definitions bundle `Q146C008` of this split); `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proofs of `OAI.CircleDomainRigidity.barrier_modulus_lower_bound` and `OAI.CircleDomainRigidity.prescribed_countable_law_of_no_small_level_barrier` of this split import it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Modulus/FilledFirstArrivalBarrier.lean (declaration OAI.CircleDomainRigidity.exists_filled_first_arrival_barrier_potential)

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C008

section

attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rd554c3_1 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_filled_first_arrival_barrier_potential
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hUB : Disjoint d.quotientDomain B) (hBU : Bᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (E : Set Sphere) (hE : IsClosed E) (hEU : E ⊆ d.quotientDomain)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π B p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint E (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hm₂ : (∑' x, m x ^ 2) ≠ ∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hunit : ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) → ρ.val ⊥ ∈ E → ρ.val ⊤ = p →
      (∀t < (⊤ : PathTime), ρ.val t ≠ p) →
      GateRules (fun j => frontier (D j).region)
        (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) ρ.val →
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m) :
    ∃k : ℕ, ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞, ∃u : Sphere → ℝ,
      IsOpen O ∧ closure O ⊆ d.quotientDomain ∧ Disjoint E (closure O) ∧
      (∀x : d.quotientDomain, x.val ∈ closure O → f x ∉ W₁) ∧
      Measurable g₁ ∧ (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
      (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
      (∀x, u x ∈ Icc 0 1) ∧ (∀x ∈ E, u x = 0) ∧
      (∀x ∈ closure (D k).region, u x = 1) ∧
      (∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
        ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g₁ m Γ.1) ∧
      ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
        liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s := by
  sorry

end CircleDomainRigidity

end

end OAI
end
