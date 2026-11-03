-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_sourceFockHamiltonian_fockInclusion_s50
-- name    : OAI.Laughlin.Fock.sourceFockHamiltonian_fockInclusion_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:44:37.174201+00:00
-- url     : https://prove2.me/theorems/0881b658-4612-4bfd-b82c-b190c723fc65
-- title:
--   OAI.Laughlin.Fock.sourceFockHamiltonian_fockInclusion_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.sourceFockHamiltonian_fockInclusion` of [lean/OAI/Analysis/Laughlin/Planar/DegreeRestriction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Planar/DegreeRestriction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem sourceFockHamiltonian_fockInclusion_s50 (L Q : ℕ) (hQ : L+2 ≤ Q)
--       (x : Space L) (hx : DegreeAtMost L L x) :
--       sourceFockHamiltonian Q (fockInclusion L Q (by omega) x) =
--         fockInclusion L Q (by omega) (restrictedSphereHamiltonian L Q x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.DegreeAtMost` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Fock.fockInclusion` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Fock.restrictedSphereHamiltonian` and `OAI.Laughlin.Fock.sourceFockHamiltonian` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Planar.finite_degree_endpoint_of_fock_square_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Planar/DegreeRestriction.lean (declaration OAI.Laughlin.Fock.sourceFockHamiltonian_fockInclusion)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sourceFockHamiltonian_fockInclusion_s50 (L Q : ℕ) (hQ : L+2 ≤ Q)
    (x : Space L) (hx : DegreeAtMost L L x) :
    sourceFockHamiltonian Q (fockInclusion L Q (by omega) x) =
      fockInclusion L Q (by omega) (restrictedSphereHamiltonian L Q x) := by
  sorry

end Laughlin.Fock

end OAI
end
