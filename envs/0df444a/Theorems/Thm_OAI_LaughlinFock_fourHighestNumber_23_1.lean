-- Prove2me | Theorems.Thm_OAI_LaughlinFock_fourHighestNumber_23_1
-- name    : OAI.LaughlinFock.fourHighestNumber_23_1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:59:55.942828+00:00
-- url     : https://prove2.me/theorems/e0529d34-e9d3-411f-b2d8-4039e9fafb6c
-- title:
--   OAI.LaughlinFock.fourHighestNumber_23_1: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LaughlinFock.fourHighestNumber_23_1` of [lean/OAI/Analysis/LaughlinFock/Certificate23.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate23.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LaughlinFock`, with `open scoped BigOperators Matrix ComplexOrder`):
--
--   ```lean
--   theorem fourHighestNumber_23_1 : ∀ A∈highestFourOccupations 23,
--       kernelHighestEntry 23 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_23 1 A
--   ```
--
--   **Definitions.** The statement is written with `OAI.LaughlinFock.highestFourOccupations` and `OAI.LaughlinFock.highestLookup` (definitions bundle `OAIQ084L000` of this split); `OAI.LaughlinFock.fourHighestCache_23` (definitions bundle `OAIQ084L022` of this split); `OAI.LaughlinFock.kernelHighestEntry` (definitions bundle `OAIQ084L024` of this split); `OAI.LaughlinFock.Occupation` (the published bundle `Def_LaughlinFock`).
--
--   **Used by.** The proof of `OAI.LaughlinFock.integer_certificate_23` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate23.lean (declaration OAI.LaughlinFock.fourHighestNumber_23_1)

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L022
import Definitions.Def_OAIQ084L024

section

attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourHighestNumber_23_1 : ∀ A∈highestFourOccupations 23,
    kernelHighestEntry 23 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_23 1 A := by
  sorry

end LaughlinFock
end

end OAI
end
