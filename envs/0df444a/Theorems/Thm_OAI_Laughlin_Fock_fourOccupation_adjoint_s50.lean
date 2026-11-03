-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_fourOccupation_adjoint_s50
-- name    : OAI.Laughlin.Fock.fourOccupation_adjoint_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:42:40.587551+00:00
-- url     : https://prove2.me/theorems/5cb9e8e0-c2d1-4992-882a-1e04688bb257
-- title:
--   OAI.Laughlin.Fock.fourOccupation_adjoint_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.fourOccupation_adjoint` of [lean/OAI/Analysis/Laughlin/FourBody/ColumnExpansion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/ColumnExpansion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`, `open Spin`):
--
--   ```lean
--   theorem fourOccupation_adjoint_s50 (Q D : ℕ) (A : FourOccupation Q D) (x y : Space Q) :
--       occupationInner Q x (fourOccupationCreate Q D A y) =
--         occupationInner Q (fourOccupationEnd Q D A x) y
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.FourOccupation` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Fock.occupationInner` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.fourOccupationCreate` and `OAI.Laughlin.Fock.fourOccupationEnd` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.limitFourCopyEnd_matrix_expansion_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/ColumnExpansion.lean (declaration OAI.Laughlin.Fock.fourOccupation_adjoint)

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

theorem fourOccupation_adjoint_s50 (Q D : ℕ) (A : FourOccupation Q D) (x y : Space Q) :
    occupationInner Q x (fourOccupationCreate Q D A y) =
      occupationInner Q (fourOccupationEnd Q D A x) y := by
  sorry

end Laughlin.Fock

end OAI
end
