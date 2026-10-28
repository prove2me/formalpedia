-- Prove2me | Theorems.Thm_OAI_Coulomb_atom_global_sector_minimum
-- name    : OAI.Coulomb.atom_global_sector_minimum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:04:20.886026+00:00
-- url     : https://prove2.me/theorems/28cc693b-c0ea-4072-ae43-eb36d7a8b435
-- title:
--   OAI.Coulomb.atom_global_sector_minimum: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Coulomb.atom_global_sector_minimum` of [lean/OAI/Analysis/CoulombRadii/SpectralTheory/GlobalSectorMinimum.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/SpectralTheory/GlobalSectorMinimum.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Coulomb`, with `open MeasureTheory Filter Set`, `open scoped ENNReal NNReal Topology BigOperators Classical`):
--
--   ```lean
--   lemma atom_global_sector_minimum (Z:ℕ) (hZ:1≤Z):
--       ∃ n:ℕ,0<n ∧ n≤3*Z ∧ ∃ u:H1Vector n,Antisymmetric u ∧ mass u=1 ∧
--         (form (atom Z hZ) u:EReal)=unrestrictedFormBottom (atom Z hZ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Coulomb.Antisymmetric`, `OAI.Coulomb.H1Vector`, `OAI.Coulomb.form` and `OAI.Coulomb.mass` (definitions bundle `OAIQ062C000` of this split); `OAI.Coulomb.atom` and `OAI.Coulomb.unrestrictedFormBottom` (definitions bundle `OAIQ062C004` of this split).
--
--   **Used by.** The proof of `OAI.NeutralAtom.physical_neutral_energy_offset` of this split imports it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/SpectralTheory/GlobalSectorMinimum.lean (declaration OAI.Coulomb.atom_global_sector_minimum)

import Mathlib
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
namespace Coulomb
lemma atom_global_sector_minimum (Z:ℕ) (hZ:1≤Z):
    ∃ n:ℕ,0<n ∧ n≤3*Z ∧ ∃ u:H1Vector n,Antisymmetric u ∧ mass u=1 ∧
      (form (atom Z hZ) u:EReal)=unrestrictedFormBottom (atom Z hZ) := by
  sorry
end Coulomb
end

end

end OAI
end
