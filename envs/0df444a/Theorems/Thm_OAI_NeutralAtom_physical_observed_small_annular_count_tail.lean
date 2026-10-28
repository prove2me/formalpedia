-- Prove2me | Theorems.Thm_OAI_NeutralAtom_physical_observed_small_annular_count_tail
-- name    : OAI.NeutralAtom.physical_observed_small_annular_count_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:13:00.900662+00:00
-- url     : https://prove2.me/theorems/d6bc49ac-ddd7-4237-9239-2dfac8d01c07
-- title:
--   OAI.NeutralAtom.physical_observed_small_annular_count_tail: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NeutralAtom.physical_observed_small_annular_count_tail` of [lean/OAI/Analysis/CoulombRadii/RandomFields/ObservationAnnulusTail.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/RandomFields/ObservationAnnulusTail.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NeutralAtom`, with `open MeasureTheory Set Filter`, `open scoped BigOperators ENNReal NNReal Classical`):
--
--   ```lean
--   theorem physical_observed_small_annular_count_tail {α A B β : ℝ}
--       (hα : 0<α) (hαA : α<A) (hAB : A<B) (hBβ : B<β) :
--       ∃ K : ℝ, 0<K ∧ ∀ D₀ : ℝ, 0≤D₀ → ∃ s : ℝ, 0 < s ∧
--       ∀ {n J : ℕ} (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n},
--       FormDomain ψ g → normSquared ψ=1 →
--       (∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h) →
--       ∀ {E : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
--       energy Z ψ g≤E+D₀ → ∀ (r : Fin J → ℝ) (k : Fin J), 0 < r k → r k < s →
--       (observationLaw J (rawLaw ψ)).real
--         {sample | K/(r k)^3 < rawCount {z : Position | A*r k≤‖z‖ ∧ ‖z‖≤B*r k}
--           (observedOrdered r k sample)}≤(r k)^40
--   ```
--
--   **Definitions.** The statement is written with `OAI.NeutralAtom.ObservationNoise`, `OAI.NeutralAtom.ObservationSample`, `OAI.NeutralAtom.observationLaw`, `OAI.NeutralAtom.observedOrdered`, `OAI.NeutralAtom.rawCount` and `OAI.NeutralAtom.rawLaw` (definitions bundle `OAIQ062C002` of this split); `OAI.Coulomb.atom` and `OAI.Coulomb.unrestrictedFormBottom` (definitions bundle `OAIQ062C004` of this split); `OAI.NeutralAtom.Configuration`, `OAI.NeutralAtom.FormDomain`, `OAI.NeutralAtom.Gradient`, `OAI.NeutralAtom.Position`, `OAI.NeutralAtom.Wavefunction`, `OAI.NeutralAtom.energy` and `OAI.NeutralAtom.normSquared` (the published bundle `Def_CoulombRadii`).
--
--   **Used by.** The proofs of `OAI.NeutralAtom.physical_propagation_good_events` and `OAI.NeutralAtom.physical_tf_band` of this split import it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/RandomFields/ObservationAnnulusTail.lean (declaration OAI.NeutralAtom.physical_observed_small_annular_count_tail)

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C002
import Definitions.Def_OAIQ062C004

section

attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

theorem physical_observed_small_annular_count_tail {α A B β : ℝ}
    (hα : 0<α) (hαA : α<A) (hAB : A<B) (hBβ : B<β) :
    ∃ K : ℝ, 0<K ∧ ∀ D₀ : ℝ, 0≤D₀ → ∃ s : ℝ, 0 < s ∧
    ∀ {n J : ℕ} (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n},
    FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D₀ → ∀ (r : Fin J → ℝ) (k : Fin J), 0 < r k → r k < s →
    (observationLaw J (rawLaw ψ)).real
      {sample | K/(r k)^3 < rawCount {z : Position | A*r k≤‖z‖ ∧ ‖z‖≤B*r k}
        (observedOrdered r k sample)}≤(r k)^40 := by
  sorry
end NeutralAtom
end

end
end

end OAI
end
