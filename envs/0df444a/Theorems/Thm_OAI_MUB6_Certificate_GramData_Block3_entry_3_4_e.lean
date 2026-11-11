-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_4_e
-- name    : OAI.MUB6.Certificate.GramData.Block3.entry_3_4_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T09:33:53.94907+00:00
-- url     : https://prove2.me/theorems/766e4703-51aa-438f-a7fe-0a0a4d591df7
-- title:
--   OAI.MUB6.Certificate.GramData.Block3.entry_3_4_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramData.Block3.entry_3_4` of [lean/OAI/Analysis/MutuallyUnbiased/GramData/Block3Check3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramData/Block3Check3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramData.Block3`, with `open Matrix`, `open scoped BigOperators`):
--
--   ```lean
--   theorem entry_3_4_e : Z 3 4 =
--       ∑ k : Fin 27, lowerUnit entries k 3 * D k * lowerUnit entries k 4
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.GramData.Block3.D`, `OAI.MUB6.Certificate.GramData.Block3.Z` and `OAI.MUB6.Certificate.GramData.Block3.entries` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.lowerUnit` (definitions bundle `OAIQ106E147` of this split).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.GramData.Block3.gram_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramData/Block3Check3.lean (declaration OAI.MUB6.Certificate.GramData.Block3.entry_3_4)

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_3_4_e : Z 3 4 =
    ∑ k : Fin 27, lowerUnit entries k 3 * D k * lowerUnit entries k 4 := by
  sorry

end MUB6.Certificate.GramData.Block3

end OAI
end
