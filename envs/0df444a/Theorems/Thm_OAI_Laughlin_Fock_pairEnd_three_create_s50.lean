-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_pairEnd_three_create_s50
-- name    : OAI.Laughlin.Fock.pairEnd_three_create_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T18:44:14.944814+00:00
-- url     : https://prove2.me/theorems/c04e4add-6cb4-4269-bb93-9e53cf531ab5
-- title:
--   OAI.Laughlin.Fock.pairEnd_three_create_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.pairEnd_three_create` of [lean/OAI/Analysis/Laughlin/ThreeBody/Contraction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/Contraction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem pairEnd_three_create_s50 (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
--       (i j k : Fin (Q+1)) :
--       pairEnd Q c (create i (create j (create k (1 : Space Q)))) =
--         (c i j-c j i) • create k (1 : Space Q) -
--         (c i k-c k i) • create j (1 : Space Q) +
--         (c j k-c k j) • create i (1 : Space Q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.create` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.pairEnd` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.threeBodyColumn_gram_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/Contraction.lean (declaration OAI.Laughlin.Fock.pairEnd_three_create)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L006
import Definitions.Def_OAIQ050L007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem pairEnd_three_create_s50 (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (i j k : Fin (Q+1)) :
    pairEnd Q c (create i (create j (create k (1 : Space Q)))) =
      (c i j-c j i) • create k (1 : Space Q) -
      (c i k-c k i) • create j (1 : Space Q) +
      (c j k-c k j) • create i (1 : Space Q) := by
  sorry

end Laughlin.Fock

end OAI
end
