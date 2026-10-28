-- Prove2me | Theorems.Thm_OAI_Coulomb_atom_strict_binding_attained
-- name    : OAI.Coulomb.atom_strict_binding_attained
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:07:06.904326+00:00
-- url     : https://prove2.me/theorems/d316ca3f-04ba-43ab-84d0-967616ee0b18
-- title:
--   OAI.Coulomb.atom_strict_binding_attained: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Coulomb.atom_strict_binding_attained` of [lean/OAI/Analysis/CoulombRadii/SpectralTheory/StrictBinding.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/SpectralTheory/StrictBinding.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Coulomb`, with `open MeasureTheory Filter Set`, `open scoped ENNReal NNReal Topology BigOperators Classical`):
--
--   ```lean
--   lemma atom_strict_binding_attained (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ} (hn:0<n)
--       (hstrict:sectorFormBottom (atom Z hZ) n < sectorFormBottom (atom Z hZ) (n-1)) :
--       ∃ u:H1Vector n,Antisymmetric u ∧ mass u=1 ∧
--         (form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) n
--   ```
--
--   **Definitions.** The statement is written with `OAI.Coulomb.Antisymmetric`, `OAI.Coulomb.H1Vector`, `OAI.Coulomb.form` and `OAI.Coulomb.mass` (definitions bundle `OAIQ062C000` of this split); `OAI.Coulomb.atom` and `OAI.Coulomb.sectorFormBottom` (definitions bundle `OAIQ062C004` of this split).
--
--   **Used by.** The proof of `OAI.Coulomb.atom_global_sector_minimum` of this split imports it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/SpectralTheory/StrictBinding.lean (declaration OAI.Coulomb.atom_strict_binding_attained)

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

lemma atom_strict_binding_attained (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ} (hn:0<n)
    (hstrict:sectorFormBottom (atom Z hZ) n < sectorFormBottom (atom Z hZ) (n-1)) :
    ∃ u:H1Vector n,Antisymmetric u ∧ mass u=1 ∧
      (form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) n := by
  sorry
end Coulomb
end

end

end OAI
end
