-- Prove2me | Theorems.Thm_OAI_Coulomb_atomic_predecessor_from_physical_mean
-- name    : OAI.Coulomb.atomic_predecessor_from_physical_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:12:27.835105+00:00
-- url     : https://prove2.me/theorems/8564b037-cbad-47cf-ba09-8d543593590a
-- title:
--   OAI.Coulomb.atomic_predecessor_from_physical_mean: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Coulomb.atomic_predecessor_from_physical_mean` of [lean/OAI/Analysis/CoulombRadii/SpectralTheory/CorePredecessor.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/SpectralTheory/CorePredecessor.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Coulomb`, with `open MeasureTheory Set Filter`, `open scoped BigOperators ENNReal NNReal Classical`):
--
--   ```lean
--   theorem atomic_predecessor_from_physical_mean : ∃ C : ℝ, 0≤C ∧
--       ∀ (Z : ℕ) (hZ : 1≤Z) {n : ℕ} (u : H1Vector n),
--       Antisymmetric u → mass u=1 →
--       ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom (atom Z hZ) → form (atom Z hZ) u≤E →
--       ∀ {t : ℝ}, 0<t → expectedPopulation u (Metric.ball 0 (2*t))≤(Z:ℝ)-1 →
--       (sectorFormBottom (atom Z hZ) (Z-1)).toReal≤
--         E+NeutralAtom.fixedCoreMomentBound t*C*((screenMass 0 (t/4))^2/t+screenMass 0 t/t^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Coulomb.Antisymmetric`, `OAI.Coulomb.H1Vector`, `OAI.Coulomb.Space`, `OAI.Coulomb.expectedPopulation`, `OAI.Coulomb.form` and `OAI.Coulomb.mass` (definitions bundle `OAIQ062C000` of this split); `OAI.Coulomb.screenMass` (definitions bundle `OAIQ062C001` of this split); `OAI.Coulomb.atom`, `OAI.Coulomb.sectorFormBottom` and `OAI.Coulomb.unrestrictedFormBottom` (definitions bundle `OAIQ062C004` of this split); `OAI.NeutralAtom.fixedCoreMomentBound` (definitions bundle `OAIQ062C008` of this split).
--
--   **Used by.** The proof of `OAI.NeutralAtom.physical_neutral_energy_offset` of this split imports it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/SpectralTheory/CorePredecessor.lean (declaration OAI.Coulomb.atomic_predecessor_from_physical_mean)

import Mathlib
import Definitions.Def_OAIQ062C008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

theorem atomic_predecessor_from_physical_mean : ∃ C : ℝ, 0≤C ∧
    ∀ (Z : ℕ) (hZ : 1≤Z) {n : ℕ} (u : H1Vector n),
    Antisymmetric u → mass u=1 →
    ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom (atom Z hZ) → form (atom Z hZ) u≤E →
    ∀ {t : ℝ}, 0<t → expectedPopulation u (Metric.ball 0 (2*t))≤(Z:ℝ)-1 →
    (sectorFormBottom (atom Z hZ) (Z-1)).toReal≤
      E+NeutralAtom.fixedCoreMomentBound t*C*((screenMass 0 (t/4))^2/t+screenMass 0 t/t^2) := by
  sorry

end Coulomb
end

end

end OAI
end
