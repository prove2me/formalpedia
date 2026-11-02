-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_13_19
-- name    : OAI.MUB6.Certificate.GramData.Block3.entry_13_19
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T15:45:58.110575+00:00
-- url     : https://prove2.me/theorems/1558f004-d242-40e4-8b56-887b4e1aa33e
-- title:
--   OAI.MUB6.Certificate.GramData.Block3.entry_13_19: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramData.Block3.entry_13_19` of [lean/OAI/Analysis/MutuallyUnbiased/GramData/Block3Check15.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramData/Block3Check15.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramData.Block3`, with `open Matrix`, `open scoped BigOperators`):
--
--   ```lean
--   theorem entry_13_19 : Z 13 19 =
--       ∑ k : Fin 27, lowerUnit entries k 13 * D k * lowerUnit entries k 19
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.GramData.Block3.D`, `OAI.MUB6.Certificate.GramData.Block3.Z` and `OAI.MUB6.Certificate.GramData.Block3.entries` (definitions bundle `OAIQ106D001` of this split); `OAI.MUB6.Certificate.lowerUnit` (definitions bundle `OAIQ106D067` of this split).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.GramData.Block3.gram` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramData/Block3Check15.lean (declaration OAI.MUB6.Certificate.GramData.Block3.entry_13_19)

import Mathlib
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D067

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_13_19 : Z 13 19 =
    ∑ k : Fin 27, lowerUnit entries k 13 * D k * lowerUnit entries k 19 := by
  sorry

end MUB6.Certificate.GramData.Block3

end OAI
end
