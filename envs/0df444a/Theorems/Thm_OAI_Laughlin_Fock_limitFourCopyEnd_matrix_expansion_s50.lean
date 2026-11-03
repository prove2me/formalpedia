-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_limitFourCopyEnd_matrix_expansion_s50
-- name    : OAI.Laughlin.Fock.limitFourCopyEnd_matrix_expansion_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:43:49.003892+00:00
-- url     : https://prove2.me/theorems/d8ec74c1-51ce-431e-b42a-24582ca8f6e3
-- title:
--   OAI.Laughlin.Fock.limitFourCopyEnd_matrix_expansion_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.limitFourCopyEnd_matrix_expansion` of [lean/OAI/Analysis/Laughlin/FourBody/LimitPositive.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/LimitPositive.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped Matrix BigOperators ComplexOrder`, `open Matrix Spin`):
--
--   ```lean
--   theorem limitFourCopyEnd_matrix_expansion_s50 (Q D : ℕ) (i : Fin ((D+1)/2)) (x : Space Q) :
--       limitFourCopyEnd Q (Certificate.copyLabel i) D x =
--         ∑ A : FourOccupation Q D, star (physicalFourOccupationColumns Q D A i) • fourOccupationEnd Q D A x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Certificate.copyLabel` (definitions bundle `OAIQ050L002` of this split); `OAI.Laughlin.Fock.FourOccupation` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Fock.fourOccupationEnd`, `OAI.Laughlin.Fock.limitFourCopyEnd` and `OAI.Laughlin.Fock.physicalFourOccupationColumns` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.source_fourBody_limitpositive_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/LimitPositive.lean (declaration OAI.Laughlin.Fock.limitFourCopyEnd_matrix_expansion)

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
open scoped Matrix BigOperators ComplexOrder
open Matrix Spin

theorem limitFourCopyEnd_matrix_expansion_s50 (Q D : ℕ) (i : Fin ((D+1)/2)) (x : Space Q) :
    limitFourCopyEnd Q (Certificate.copyLabel i) D x =
      ∑ A : FourOccupation Q D, star (physicalFourOccupationColumns Q D A i) • fourOccupationEnd Q D A x := by
  sorry

end Laughlin.Fock

end OAI
end
