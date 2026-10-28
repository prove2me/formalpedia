-- Prove2me | Theorems.Thm_OAI_NeutralAtom_physical_retained_spatial_cap
-- name    : OAI.NeutralAtom.physical_retained_spatial_cap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:16:52.679996+00:00
-- url     : https://prove2.me/theorems/9e54486b-1f70-4d58-b433-82e75c3bdba4
-- title:
--   OAI.NeutralAtom.physical_retained_spatial_cap: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NeutralAtom.physical_retained_spatial_cap` of [lean/OAI/Analysis/CoulombRadii/Screening/PhysicalSpatialCap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/Screening/PhysicalSpatialCap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NeutralAtom`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal BigOperators Classical SchwartzMap`):
--
--   ```lean
--   theorem physical_retained_spatial_cap {L : ℝ} (hL : 1 ≤ L) :
--       ∃ C : ℝ,0 < C ∧
--       ∀ (g₀ : 𝓢(Position,ℝ)), (∀ z,1 < ‖z‖ → g₀ z=0) → (∫ z,g₀ z^2)=1 →
--       (∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖)) →
--       ∀ {n J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n},
--       ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
--       (∀ (χ : Wavefunction n) (h : Gradient n),FormDomain χ h → normSquared χ=1 →
--         energy Z ψ g ≤ energy Z χ h) →
--       ∀ {E D : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
--       energy Z ψ g ≤ E+D → 0 ≤ D →
--       ∀ {c r₀ s : ℝ},0 < c → 0 < r₀ → 0 < s →
--       c*(1+packetExponent)*s^packetExponent ≤ 1/2 →
--       100000*c*s^packetExponent ≤ 10 →
--       (8*L/100000)*s ≤ 1 → D*((8*L/100000)*s)^7 ≤ 1 →
--       ∀ (j : ℕ),r₀*2^j ≤ s →
--       letI := rawLaw_isProbability hd.2.2.1 hn
--       let P := observationLaw J (rawLaw ψ)
--       let r := fun k : Fin J =>  r₀*2^k.val
--       ∃ G : Set (ObservationSample n J),(MeasurableSet G ∧
--         MeasurableSet[MeasurableSpace.comap (tailObservation r j) inferInstance] G) ∧
--         P.real Gᶜ ≤ C*(r₀*2^j)^249 ∧
--         ∀ z∈G,∀ y : Position,3*(r₀*2^j)/4 ≤ ‖y‖ → ‖y‖ ≤ 6*L*(r₀*2^j) →
--           ‖y‖^4*((Z:ℝ)*coulombKernel y-potentialOf
--             (conditionalPacketDensity P Prod.fst (tailObservation r j) g₀ c r₀ s
--               (tailObservation r j z)) y) ≤ physicalSpatialCap
--   ```
--
--   **Definitions.** The statement is written with `OAI.NeutralAtom.coulombKernel` and `OAI.NeutralAtom.potentialOf` (definitions bundle `OAIQ062C001` of this split); `OAI.NeutralAtom.ObservationNoise`, `OAI.NeutralAtom.ObservationSample`, `OAI.NeutralAtom.UnorderedArray`, `OAI.NeutralAtom.conditionalPacketDensity`, `OAI.NeutralAtom.observationLaw`, `OAI.NeutralAtom.packetExponent`, `OAI.NeutralAtom.rawLaw`, `OAI.NeutralAtom.rawLaw_isProbability`, `OAI.NeutralAtom.tailObservation` and `OAI.NeutralAtom.unorderedArrayMeasurable` (definitions bundle `OAIQ062C002` of this split); `OAI.Coulomb.atom` and `OAI.Coulomb.unrestrictedFormBottom` (definitions bundle `OAIQ062C004` of this split); `OAI.NeutralAtom.observationLaw_probability` (definitions bundle `OAIQ062C005` of this split); `OAI.NeutralAtom.physicalSpatialCap` (definitions bundle `OAIQ062C008` of this split); `OAI.NeutralAtom.Configuration`, `OAI.NeutralAtom.FormDomain`, `OAI.NeutralAtom.Gradient`, `OAI.NeutralAtom.HasWeakGradient`, `OAI.NeutralAtom.IsAntisymmetric`, `OAI.NeutralAtom.Position`, `OAI.NeutralAtom.Spins`, `OAI.NeutralAtom.Wavefunction`, `OAI.NeutralAtom.energy` and `OAI.NeutralAtom.normSquared` (the published bundle `Def_CoulombRadii`).
--
--   **Used by.** The proofs of `OAI.NeutralAtom.physical_propagation_good_events` and `OAI.NeutralAtom.physical_tf_band` of this split import it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/Screening/PhysicalSpatialCap.lean (declaration OAI.NeutralAtom.physical_retained_spatial_cap)

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008

section

attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_retained_spatial_cap {L : ℝ} (hL : 1 ≤ L) :
    ∃ C : ℝ,0 < C ∧
    ∀ (g₀ : 𝓢(Position,ℝ)), (∀ z,1 < ‖z‖ → g₀ z=0) → (∫ z,g₀ z^2)=1 →
    (∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖)) →
    ∀ {n J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction n) (h : Gradient n),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E D : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → 0 ≤ D →
    ∀ {c r₀ s : ℝ},0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/2 →
    100000*c*s^packetExponent ≤ 10 →
    (8*L/100000)*s ≤ 1 → D*((8*L/100000)*s)^7 ≤ 1 →
    ∀ (j : ℕ),r₀*2^j ≤ s →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r := fun k : Fin J =>  r₀*2^k.val
    ∃ G : Set (ObservationSample n J),(MeasurableSet G ∧
      MeasurableSet[MeasurableSpace.comap (tailObservation r j) inferInstance] G) ∧
      P.real Gᶜ ≤ C*(r₀*2^j)^249 ∧
      ∀ z∈G,∀ y : Position,3*(r₀*2^j)/4 ≤ ‖y‖ → ‖y‖ ≤ 6*L*(r₀*2^j) →
        ‖y‖^4*((Z:ℝ)*coulombKernel y-potentialOf
          (conditionalPacketDensity P Prod.fst (tailObservation r j) g₀ c r₀ s
            (tailObservation r j z)) y) ≤ physicalSpatialCap := by
  sorry
end NeutralAtom
end

end

end OAI
end
