-- Prove2me | Theorems.Thm_OAI_NeutralAtom_physical_neutral_energy_offset
-- name    : OAI.NeutralAtom.physical_neutral_energy_offset
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:07:49.943367+00:00
-- url     : https://prove2.me/theorems/0f77293e-f53e-47d0-abd0-b839d2f85143
-- title:
--   OAI.NeutralAtom.physical_neutral_energy_offset: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NeutralAtom.physical_neutral_energy_offset` of [lean/OAI/Analysis/CoulombRadii/LimitTheory/NeutralBaseline.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/LimitTheory/NeutralBaseline.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NeutralAtom`, with `open MeasureTheory Filter Set`, `open scoped ENNReal NNReal Topology BigOperators Classical`):
--
--   ```lean
--   theorem physical_neutral_energy_offset : ∃ D:ℝ,0≤D ∧ ∃ Zmin:ℕ,
--       ∀ Z:ℕ,Zmin≤Z → ∀ hZ:1≤Z,
--       ∀ {ψ:Wavefunction Z} {g:Gradient Z},FormDomain ψ g → normSquared ψ=1 →
--       (∀ (χ:Wavefunction Z) (h:Gradient Z),FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h) →
--       energy Z ψ g ≤ (Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ)).toReal+D
--   ```
--
--   **Definitions.** The statement is written with `OAI.Coulomb.atom` and `OAI.Coulomb.unrestrictedFormBottom` (definitions bundle `OAIQ062C004` of this split); `OAI.NeutralAtom.FormDomain`, `OAI.NeutralAtom.Gradient`, `OAI.NeutralAtom.Wavefunction`, `OAI.NeutralAtom.energy` and `OAI.NeutralAtom.normSquared` (the published bundle `Def_CoulombRadii`).
--
--   **Used by.** The proofs of `OAI.NeutralAtom.generalized_outer_radii` and `OAI.NeutralAtom.quantum_profile_packet_limit` of this split import it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/LimitTheory/NeutralBaseline.lean (declaration OAI.NeutralAtom.physical_neutral_energy_offset)

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace NeutralAtom

theorem physical_neutral_energy_offset : ∃ D:ℝ,0≤D ∧ ∃ Zmin:ℕ,
    ∀ Z:ℕ,Zmin≤Z → ∀ hZ:1≤Z,
    ∀ {ψ:Wavefunction Z} {g:Gradient Z},FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ:Wavefunction Z) (h:Gradient Z),FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h) →
    energy Z ψ g ≤ (Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ)).toReal+D := by
  sorry
end NeutralAtom
end

end

end OAI
end
