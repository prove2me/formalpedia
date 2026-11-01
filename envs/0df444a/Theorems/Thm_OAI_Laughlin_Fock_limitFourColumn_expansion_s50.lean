-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_limitFourColumn_expansion_s50
-- name    : OAI.Laughlin.Fock.limitFourColumn_expansion_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:43:03.6383+00:00
-- url     : https://prove2.me/theorems/c2eade05-75e0-47eb-bac4-6a42eea15242
-- title:
--   OAI.Laughlin.Fock.limitFourColumn_expansion_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.limitFourColumn_expansion` of [lean/OAI/Analysis/Laughlin/FourBody/ColumnExpansion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/ColumnExpansion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`, `open Spin`):
--
--   ```lean
--   theorem limitFourColumn_expansion_s50 (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r) :
--       limitFourColumn Q r D = ∑ A : FourOccupation Q D,
--         (fourOccupationCoefficient Q r D A.val : ℂ) • occupationBasis Q A.val
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.FourOccupation` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Fock.fourOccupationCoefficient` and `OAI.Laughlin.Fock.limitFourColumn` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space` and `OAI.Laughlin.Fock.occupationBasis` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.limitFourCopyEnd_matrix_expansion_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/ColumnExpansion.lean (declaration OAI.Laughlin.Fock.limitFourColumn_expansion)

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
open Spin

theorem limitFourColumn_expansion_s50 (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r) :
    limitFourColumn Q r D = ∑ A : FourOccupation Q D,
      (fourOccupationCoefficient Q r D A.val : ℂ) • occupationBasis Q A.val := by
  sorry

end Laughlin.Fock

end OAI
end
