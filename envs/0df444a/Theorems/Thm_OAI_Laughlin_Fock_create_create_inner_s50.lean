-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_create_create_inner_s50
-- name    : OAI.Laughlin.Fock.create_create_inner_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T18:43:46.322473+00:00
-- url     : https://prove2.me/theorems/90c0e6aa-1455-41a0-866e-5af57c5da086
-- title:
--   OAI.Laughlin.Fock.create_create_inner_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.create_create_inner` of [lean/OAI/Analysis/Laughlin/Operators/RowNormalSquare.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Operators/RowNormalSquare.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem create_create_inner_s50 (Q : ℕ) (i j : Fin (Q+1)) (y z : Space Q) :
--       occupationInner Q (create i y) (create j z) =
--         delta i j * occupationInner Q y z -
--           occupationInner Q (annihilate j y) (annihilate i z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.create`, `OAI.Laughlin.Fock.delta` and `OAI.Laughlin.Fock.occupationInner` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space` and `OAI.Laughlin.Fock.annihilate` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.row_normal_square_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Operators/RowNormalSquare.lean (declaration OAI.Laughlin.Fock.create_create_inner)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem create_create_inner_s50 (Q : ℕ) (i j : Fin (Q+1)) (y z : Space Q) :
    occupationInner Q (create i y) (create j z) =
      delta i j * occupationInner Q y z -
        occupationInner Q (annihilate j y) (annihilate i z) := by
  sorry

end Laughlin.Fock

end OAI
end
