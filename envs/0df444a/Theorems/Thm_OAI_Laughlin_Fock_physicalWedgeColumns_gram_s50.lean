-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_physicalWedgeColumns_gram_s50
-- name    : OAI.Laughlin.Fock.physicalWedgeColumns_gram_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:44:58.39017+00:00
-- url     : https://prove2.me/theorems/c7ebceb5-4bb7-404d-9f51-1b56dbac88e4
-- title:
--   OAI.Laughlin.Fock.physicalWedgeColumns_gram_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.physicalWedgeColumns_gram` of [lean/OAI/Analysis/Laughlin/FourBody/WedgeCompression.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/WedgeCompression.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped Matrix BigOperators ComplexOrder`, `open Matrix Spin`):
--
--   ```lean
--   theorem physicalWedgeColumns_gram_s50 (Q D : ℕ) (hQ : D+1 ≤ Q) :
--       (physicalWedgeColumns Q D)ᴴ * physicalWedgeColumns Q D =
--         (physicalLimitGram Q D).map Complex.ofReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.physicalLimitGram` and `OAI.Laughlin.Fock.physicalWedgeColumns` (definitions bundle `OAIQ050L012` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.physicalFourOccupationColumns_positive_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/WedgeCompression.lean (declaration OAI.Laughlin.Fock.physicalWedgeColumns_gram)

import Mathlib
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

theorem physicalWedgeColumns_gram_s50 (Q D : ℕ) (hQ : D+1 ≤ Q) :
    (physicalWedgeColumns Q D)ᴴ * physicalWedgeColumns Q D =
      (physicalLimitGram Q D).map Complex.ofReal := by
  sorry

end Laughlin.Fock

end OAI
end
