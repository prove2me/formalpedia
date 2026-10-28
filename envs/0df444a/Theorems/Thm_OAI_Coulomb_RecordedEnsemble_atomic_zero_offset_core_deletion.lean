-- Prove2me | Theorems.Thm_OAI_Coulomb_RecordedEnsemble_atomic_zero_offset_core_deletion
-- name    : OAI.Coulomb.RecordedEnsemble.atomic_zero_offset_core_deletion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:04:09.544952+00:00
-- url     : https://prove2.me/theorems/30a8a1df-4abb-4cb2-ae56-91143a69c364
-- title:
--   OAI.Coulomb.RecordedEnsemble.atomic_zero_offset_core_deletion: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Coulomb.RecordedEnsemble.atomic_zero_offset_core_deletion` of [lean/OAI/Analysis/CoulombRadii/RandomFields/CoreBudget.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/RandomFields/CoreBudget.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Coulomb.RecordedEnsemble`, with `open MeasureTheory Set Filter`, `open scoped BigOperators ENNReal NNReal Classical Topology ContDiff`):
--
--   ```lean
--   theorem atomic_zero_offset_core_deletion : ∃ C : ℝ, 0≤C ∧
--       ∀ {J n : ℕ} (S : Nuclei J), (∀ j,S.position j=0) →
--       ∀ ψ : H1Vector n, Antisymmetric ψ → mass ψ=1 →
--       ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E →
--       ∀ {t : ℝ}, 0<t → ∃ T : RecordedEnsemble n,
--         T.Conserves ψ ∧ T.CoreFermionic ∧ T.CoreSupported {y | ‖y‖<2*t} ∧
--         T.OutSupported {y | t≤‖y‖} ∧ T.totalMass=1 ∧
--         T.totalCoreForm S ≤ E+C*((screenMass 0 (t/4))^2/t+screenMass 0 t/t^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Coulomb.Antisymmetric`, `OAI.Coulomb.H1Vector`, `OAI.Coulomb.Nuclei`, `OAI.Coulomb.RecordedEnsemble`, `OAI.Coulomb.Space`, `OAI.Coulomb.form`, `OAI.Coulomb.mass`, `OAI.Coulomb.RecordedEnsemble.Conserves`, `OAI.Coulomb.RecordedEnsemble.CoreFermionic`, `OAI.Coulomb.RecordedEnsemble.OutSupported` and `OAI.Coulomb.RecordedEnsemble.totalMass` (definitions bundle `OAIQ062C000` of this split); `OAI.Coulomb.screenMass` (definitions bundle `OAIQ062C001` of this split); `OAI.Coulomb.unrestrictedFormBottom`, `OAI.Coulomb.RecordedEnsemble.CoreSupported` and `OAI.Coulomb.RecordedEnsemble.totalCoreForm` (definitions bundle `OAIQ062C004` of this split).
--
--   **Used by.** The proof of `OAI.Coulomb.atomic_predecessor_from_physical_mean` of this split imports it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/RandomFields/CoreBudget.lean (declaration OAI.Coulomb.RecordedEnsemble.atomic_zero_offset_core_deletion)

import Mathlib
import Definitions.Def_OAIQ062C004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb
namespace RecordedEnsemble

theorem atomic_zero_offset_core_deletion : ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ j,S.position j=0) →
    ∀ ψ : H1Vector n, Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E →
    ∀ {t : ℝ}, 0<t → ∃ T : RecordedEnsemble n,
      T.Conserves ψ ∧ T.CoreFermionic ∧ T.CoreSupported {y | ‖y‖<2*t} ∧
      T.OutSupported {y | t≤‖y‖} ∧ T.totalMass=1 ∧
      T.totalCoreForm S ≤ E+C*((screenMass 0 (t/4))^2/t+screenMass 0 t/t^2) := by
  sorry

end RecordedEnsemble
end Coulomb
end

end

end OAI
end
