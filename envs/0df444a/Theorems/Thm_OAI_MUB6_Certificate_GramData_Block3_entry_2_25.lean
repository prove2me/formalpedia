-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_25
-- name    : OAI.MUB6.Certificate.GramData.Block3.entry_2_25
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:05:54.912384+00:00
-- url     : https://prove2.me/theorems/dbc5e2b7-98c2-431a-ad0a-8638f5bf4dd3
-- title:
--   OAI.MUB6.Certificate.GramData.Block3.entry_2_25: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramData.Block3.entry_2_25` of [lean/OAI/Analysis/MutuallyUnbiased/GramData/Block3Check3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramData/Block3Check3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramData.Block3`, with `open Matrix`, `open scoped BigOperators`):
--
--   ```lean
--   theorem entry_2_25 : Z 2 25 =
--       ∑ k : Fin 27, lowerUnit entries k 2 * D k * lowerUnit entries k 25
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.GramData.Block3.D`, `OAI.MUB6.Certificate.GramData.Block3.Z` and `OAI.MUB6.Certificate.GramData.Block3.entries` (definitions bundle `OAIQ106D001` of this split); `OAI.MUB6.Certificate.lowerUnit` (definitions bundle `OAIQ106D067` of this split).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.GramData.Block3.gram` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramData/Block3Check3.lean (declaration OAI.MUB6.Certificate.GramData.Block3.entry_2_25)

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

theorem entry_2_25 : Z 2 25 =
    ∑ k : Fin 27, lowerUnit entries k 2 * D k * lowerUnit entries k 25 := by
  sorry

end MUB6.Certificate.GramData.Block3

end OAI
end
