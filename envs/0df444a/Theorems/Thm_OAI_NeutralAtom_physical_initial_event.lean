-- Prove2me | Theorems.Thm_OAI_NeutralAtom_physical_initial_event
-- name    : OAI.NeutralAtom.physical_initial_event
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:07:39.580877+00:00
-- url     : https://prove2.me/theorems/000503b4-904a-4666-9ff9-2026f6882d1d
-- title:
--   OAI.NeutralAtom.physical_initial_event: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NeutralAtom.physical_initial_event` of [lean/OAI/Analysis/CoulombRadii/Propagation/InitialMesh.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/Propagation/InitialMesh.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NeutralAtom`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical SchwartzMap`):
--
--   ```lean
--   theorem physical_initial_event : ∃ εmax : ℝ,0<εmax ∧
--       ∀ {ε : ℝ},0<ε → ε≤εmax →
--       ∀ (D : ℝ) (g₀ : 𝓢(Position,ℝ)),(∫ w,g₀ w^2)=1 →
--       (∀ w,g₀ w=g₀ (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g₀ w=0) →
--       ∀ {c s : ℝ},0 < c → 0 < s → c*(1+packetExponent)*s^packetExponent≤1/2 →
--       ∃ Zmin : ℕ,∀ (Z : ℕ),Zmin≤Z → ∀ (hZ : 1≤Z) {N J : ℕ}
--         {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
--       ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
--       (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
--         energy Z ψ g≤energy Z χ h) →
--       ∀ {E : ℝ},(E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
--       energy Z ψ g≤E+D → (N+1:ℝ)≤3*(Z:ℝ) →
--       letI := rawLaw_isProbability hd.2.2.1 hn
--       let P := observationLaw J (rawLaw ψ)
--       let r₀ := initialAtomicRadius ε Z
--       let r := fun k : Fin J => r₀*2^k.val
--       ∃ G : Set (Fin J → UnorderedArray (N+1)),MeasurableSet G ∧
--         P.real (tailObservation r 0 ⁻¹' Gᶜ)≤343*r₀^35 ∧
--         ∀ a∈G,∀ y : Position,r₀≤‖y‖ → ‖y‖≤2*r₀ →
--           potentialOf (conditionalPacketDensity P Prod.fst (tailObservation r 0) g₀ c r₀ s a) y≤
--             (1/10:ℝ)*(Z:ℝ)/r₀
--   ```
--
--   **Definitions.** The statement is written with `OAI.NeutralAtom.potentialOf` (definitions bundle `OAIQ062C001` of this split); `OAI.NeutralAtom.ObservationNoise`, `OAI.NeutralAtom.ObservationSample`, `OAI.NeutralAtom.UnorderedArray`, `OAI.NeutralAtom.conditionalPacketDensity`, `OAI.NeutralAtom.initialAtomicRadius`, `OAI.NeutralAtom.observationLaw`, `OAI.NeutralAtom.packetExponent`, `OAI.NeutralAtom.rawLaw`, `OAI.NeutralAtom.rawLaw_isProbability`, `OAI.NeutralAtom.tailObservation` and `OAI.NeutralAtom.unorderedArrayMeasurable` (definitions bundle `OAIQ062C002` of this split); `OAI.Coulomb.atom` and `OAI.Coulomb.unrestrictedFormBottom` (definitions bundle `OAIQ062C004` of this split); `OAI.NeutralAtom.observationLaw_probability` (definitions bundle `OAIQ062C005` of this split); `OAI.NeutralAtom.Configuration`, `OAI.NeutralAtom.FormDomain`, `OAI.NeutralAtom.Gradient`, `OAI.NeutralAtom.HasWeakGradient`, `OAI.NeutralAtom.IsAntisymmetric`, `OAI.NeutralAtom.Position`, `OAI.NeutralAtom.Spins`, `OAI.NeutralAtom.Wavefunction`, `OAI.NeutralAtom.energy` and `OAI.NeutralAtom.normSquared` (the published bundle `Def_CoulombRadii`).
--
--   **Used by.** The proofs of `OAI.NeutralAtom.generalized_outer_radii` and `OAI.NeutralAtom.physical_neutral_energy_offset` of this split import it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/Propagation/InitialMesh.lean (declaration OAI.NeutralAtom.physical_initial_event)

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C004
import Definitions.Def_OAIQ062C005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology Classical SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_initial_event : ∃ εmax : ℝ,0<εmax ∧
    ∀ {ε : ℝ},0<ε → ε≤εmax →
    ∀ (D : ℝ) (g₀ : 𝓢(Position,ℝ)),(∫ w,g₀ w^2)=1 →
    (∀ w,g₀ w=g₀ (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g₀ w=0) →
    ∀ {c s : ℝ},0 < c → 0 < s → c*(1+packetExponent)*s^packetExponent≤1/2 →
    ∃ Zmin : ℕ,∀ (Z : ℕ),Zmin≤Z → ∀ (hZ : 1≤Z) {N J : ℕ}
      {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g≤energy Z χ h) →
    ∀ {E : ℝ},(E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → (N+1:ℝ)≤3*(Z:ℝ) →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r₀ := initialAtomicRadius ε Z
    let r := fun k : Fin J => r₀*2^k.val
    ∃ G : Set (Fin J → UnorderedArray (N+1)),MeasurableSet G ∧
      P.real (tailObservation r 0 ⁻¹' Gᶜ)≤343*r₀^35 ∧
      ∀ a∈G,∀ y : Position,r₀≤‖y‖ → ‖y‖≤2*r₀ →
        potentialOf (conditionalPacketDensity P Prod.fst (tailObservation r 0) g₀ c r₀ s a) y≤
          (1/10:ℝ)*(Z:ℝ)/r₀ := by
  sorry
end NeutralAtom
end

end

end OAI
end
