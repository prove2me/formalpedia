-- Prove2me | Theorems.Thm_OAI_NeutralAtom_physical_tf_band
-- name    : OAI.NeutralAtom.physical_tf_band
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:20:03.867507+00:00
-- url     : https://prove2.me/theorems/2960fad3-a666-44e0-9a86-74c720983e94
-- title:
--   OAI.NeutralAtom.physical_tf_band: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NeutralAtom.physical_tf_band` of [lean/OAI/Analysis/CoulombRadii/ThomasFermi/InverseDensityError.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/ThomasFermi/InverseDensityError.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NeutralAtom`, with `open MeasureTheory Set Filter`, `open scoped BigOperators ENNReal NNReal Classical Topology`):
--
--   ```lean
--   theorem physical_tf_band {q : ℝ} (hq : 2 ≤ q) : ∃ C : ℝ,0 < C ∧
--       ∀ D : ℝ,0 ≤ D → ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧
--       ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
--       ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
--       (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
--         energy Z ψ g ≤ energy Z χ h) →
--       ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
--       energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0 < r₀ → 0 < s → s < s₀ →
--       ∀ (j : Fin J),r₀*2^j.val ≤ s →
--       letI := rawLaw_isProbability hd.2.2.1 hn
--       let P := observationLaw J (rawLaw ψ)
--       let rs := fun k : Fin J => r₀*2^k.val
--       ∃ G : Set (ObservationSample (N+1) J),MeasurableSet G ∧ P.real Gᶜ ≤ C*s^25 ∧
--         ∀ o∈G,∀ y : Position,rs j ≤ ‖y‖ → ‖y‖ ≤ 4*q^2*(rs j) →
--           let μ := conditionalPacketDensity P Prod.fst (tailObservation rs j.val)
--             Coulomb.unitWindow 1 r₀ s (tailObservation rs j.val o)
--           screenedField (Z:ℝ) μ y ≤ physicalSpatialCap/‖y‖^4 ∧
--           |μ y-tfDensityScalar (screenedField (Z:ℝ) μ y)| ≤ (q^8)⁻¹/‖y‖^6
--   ```
--
--   **Definitions.** The statement is written with `OAI.Coulomb.Space` and `OAI.Coulomb.unitWindow` (definitions bundle `OAIQ062C000` of this split); `OAI.NeutralAtom.ObservationNoise`, `OAI.NeutralAtom.ObservationSample`, `OAI.NeutralAtom.UnorderedArray`, `OAI.NeutralAtom.conditionalPacketDensity`, `OAI.NeutralAtom.observationLaw`, `OAI.NeutralAtom.rawLaw`, `OAI.NeutralAtom.rawLaw_isProbability`, `OAI.NeutralAtom.tailObservation` and `OAI.NeutralAtom.unorderedArrayMeasurable` (definitions bundle `OAIQ062C002` of this split); `OAI.Coulomb.atom` and `OAI.Coulomb.unrestrictedFormBottom` (definitions bundle `OAIQ062C004` of this split); `OAI.NeutralAtom.observationLaw_probability`, `OAI.NeutralAtom.screenedField` and `OAI.NeutralAtom.tfDensityScalar` (definitions bundle `OAIQ062C005` of this split); `OAI.NeutralAtom.physicalSpatialCap` (definitions bundle `OAIQ062C008` of this split); `OAI.NeutralAtom.Configuration`, `OAI.NeutralAtom.FormDomain`, `OAI.NeutralAtom.Gradient`, `OAI.NeutralAtom.HasWeakGradient`, `OAI.NeutralAtom.IsAntisymmetric`, `OAI.NeutralAtom.Position`, `OAI.NeutralAtom.Spins`, `OAI.NeutralAtom.Wavefunction`, `OAI.NeutralAtom.energy` and `OAI.NeutralAtom.normSquared` (the published bundle `Def_CoulombRadii`).
--
--   **Used by.** The proof of `OAI.NeutralAtom.generalized_outer_radii` of this split imports it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/ThomasFermi/InverseDensityError.lean (declaration OAI.NeutralAtom.physical_tf_band)

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
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

theorem physical_tf_band {q : ℝ} (hq : 2 ≤ q) : ∃ C : ℝ,0 < C ∧
    ∀ D : ℝ,0 ≤ D → ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0 < r₀ → 0 < s → s < s₀ →
    ∀ (j : Fin J),r₀*2^j.val ≤ s →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let rs := fun k : Fin J => r₀*2^k.val
    ∃ G : Set (ObservationSample (N+1) J),MeasurableSet G ∧ P.real Gᶜ ≤ C*s^25 ∧
      ∀ o∈G,∀ y : Position,rs j ≤ ‖y‖ → ‖y‖ ≤ 4*q^2*(rs j) →
        let μ := conditionalPacketDensity P Prod.fst (tailObservation rs j.val)
          Coulomb.unitWindow 1 r₀ s (tailObservation rs j.val o)
        screenedField (Z:ℝ) μ y ≤ physicalSpatialCap/‖y‖^4 ∧
        |μ y-tfDensityScalar (screenedField (Z:ℝ) μ y)| ≤ (q^8)⁻¹/‖y‖^6 := by
  sorry
end NeutralAtom
end

end

end OAI
end
