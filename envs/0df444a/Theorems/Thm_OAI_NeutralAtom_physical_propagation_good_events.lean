-- Prove2me | Theorems.Thm_OAI_NeutralAtom_physical_propagation_good_events
-- name    : OAI.NeutralAtom.physical_propagation_good_events
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:16:18.530624+00:00
-- url     : https://prove2.me/theorems/dd155e9e-a521-4ed7-8ce3-0ef5ac289a21
-- title:
--   OAI.NeutralAtom.physical_propagation_good_events: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NeutralAtom.physical_propagation_good_events` of [lean/OAI/Analysis/CoulombRadii/Propagation/PropagationConstants.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/Propagation/PropagationConstants.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NeutralAtom`, with `open MeasureTheory Set Filter`, `open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap`):
--
--   ```lean
--   theorem physical_propagation_good_events (g₀ : 𝓢(Position,ℝ))
--       (hg : ∀ z,1<‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
--       (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
--       {c B C : ℝ} (hc : 0 < c) (hB : 0<B) (hBC : B ≤ C) (hcapC : physicalSpatialCap ≤ C)
--       (k : PropagationConstants B C) :
--       ∃ K : ℝ,0<K ∧ ∀ D : ℝ,0 ≤ D → ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧
--         (∀ {s : ℝ},0 < s → s < s₀ → c*(1+packetExponent)*s^packetExponent ≤ 1/2 ∧
--           c*s^packetExponent ≤ 1/4 ∧ D*s^7 ≤ 1) ∧
--       ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
--       ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
--       (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
--         energy Z ψ g ≤ energy Z χ h) →
--       ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
--       energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0 < r₀ → 0 < s → s < s₀ →
--       ∀ (j : Fin J),r₀*2^j.val  ≤  s →
--       letI := rawLaw_isProbability hd.2.2.1 hn
--       let P := observationLaw J (rawLaw ψ)
--       let rs := fun l : Fin J => r₀*2^l.val
--       ∃ G : Set (ObservationSample (N+1) J),
--         (MeasurableSet G ∧ MeasurableSet[observationSigma rs j.val] G) ∧
--         P.real Gᶜ ≤ K*(rs j)^24 ∧
--         ∀ o∈G,∀ x : Position,rs j ≤ ‖x‖ → ‖x‖ ≤ 4*k.L*(rs j) →
--           let μ := conditionalPacketDensity P Prod.fst (tailObservation rs j.val) g₀ c r₀ s (tailObservation rs j.val o)
--           let F := (Z:ℝ)*coulombKernel x-potentialOf μ x
--           F ≤ C/‖x‖^4 ∧ ∀ h∈Icc (B/2) C,
--             (Coulomb.tfScalarDensity h ≤ ‖x‖^6*μ x → h-k.ξ ≤ ‖x‖^4*F) ∧
--             (‖x‖^6*μ x ≤ Coulomb.tfScalarDensity h → ‖x‖^4*F ≤ h+k.ξ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.NeutralAtom.coulombKernel` and `OAI.NeutralAtom.potentialOf` (definitions bundle `OAIQ062C001` of this split); `OAI.NeutralAtom.ObservationNoise`, `OAI.NeutralAtom.ObservationSample`, `OAI.NeutralAtom.PropagationConstants`, `OAI.NeutralAtom.UnorderedArray`, `OAI.NeutralAtom.conditionalPacketDensity`, `OAI.NeutralAtom.observationLaw`, `OAI.NeutralAtom.observationSigma`, `OAI.NeutralAtom.packetExponent`, `OAI.NeutralAtom.rawLaw`, `OAI.NeutralAtom.rawLaw_isProbability`, `OAI.NeutralAtom.tailObservation` and `OAI.NeutralAtom.unorderedArrayMeasurable` (definitions bundle `OAIQ062C002` of this split); `OAI.Coulomb.atom` and `OAI.Coulomb.unrestrictedFormBottom` (definitions bundle `OAIQ062C004` of this split); `OAI.Coulomb.tfScalarDensity` and `OAI.NeutralAtom.observationLaw_probability` (definitions bundle `OAIQ062C005` of this split); `OAI.NeutralAtom.physicalSpatialCap` (definitions bundle `OAIQ062C008` of this split); `OAI.NeutralAtom.Configuration`, `OAI.NeutralAtom.FormDomain`, `OAI.NeutralAtom.Gradient`, `OAI.NeutralAtom.HasWeakGradient`, `OAI.NeutralAtom.IsAntisymmetric`, `OAI.NeutralAtom.Position`, `OAI.NeutralAtom.Spins`, `OAI.NeutralAtom.Wavefunction`, `OAI.NeutralAtom.energy` and `OAI.NeutralAtom.normSquared` (the published bundle `Def_CoulombRadii`).
--
--   **Used by.** The proofs of `OAI.NeutralAtom.generalized_outer_radii` and `OAI.NeutralAtom.physical_neutral_energy_offset` of this split import it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/Propagation/PropagationConstants.lean (declaration OAI.NeutralAtom.physical_propagation_good_events)

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
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_propagation_good_events (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z,1<‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {c B C : ℝ} (hc : 0 < c) (hB : 0<B) (hBC : B ≤ C) (hcapC : physicalSpatialCap ≤ C)
    (k : PropagationConstants B C) :
    ∃ K : ℝ,0<K ∧ ∀ D : ℝ,0 ≤ D → ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧
      (∀ {s : ℝ},0 < s → s < s₀ → c*(1+packetExponent)*s^packetExponent ≤ 1/2 ∧
        c*s^packetExponent ≤ 1/4 ∧ D*s^7 ≤ 1) ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0 < r₀ → 0 < s → s < s₀ →
    ∀ (j : Fin J),r₀*2^j.val  ≤  s →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let rs := fun l : Fin J => r₀*2^l.val
    ∃ G : Set (ObservationSample (N+1) J),
      (MeasurableSet G ∧ MeasurableSet[observationSigma rs j.val] G) ∧
      P.real Gᶜ ≤ K*(rs j)^24 ∧
      ∀ o∈G,∀ x : Position,rs j ≤ ‖x‖ → ‖x‖ ≤ 4*k.L*(rs j) →
        let μ := conditionalPacketDensity P Prod.fst (tailObservation rs j.val) g₀ c r₀ s (tailObservation rs j.val o)
        let F := (Z:ℝ)*coulombKernel x-potentialOf μ x
        F ≤ C/‖x‖^4 ∧ ∀ h∈Icc (B/2) C,
          (Coulomb.tfScalarDensity h ≤ ‖x‖^6*μ x → h-k.ξ ≤ ‖x‖^4*F) ∧
          (‖x‖^6*μ x ≤ Coulomb.tfScalarDensity h → ‖x‖^4*F ≤ h+k.ξ) := by
  sorry
end NeutralAtom
end

end

end OAI
end
