-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block4_entries_reindex_13_e
-- name    : OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_13_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T09:43:59.84125+00:00
-- url     : https://prove2.me/theorems/620ea1b2-b496-424f-a255-e4fb297da226
-- title:
--   OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_13_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_13` of [lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block4Reindex13.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block4Reindex13.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramAssembly.Block4`):
--
--   ```lean
--   theorem entries_reindex_13_e (j : Fin 22) :
--       Integer.Sparse.reindex key (entries 13 j) = GramEntries.Block4.entries 13 j
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.GramNormalization.Key` and `OAI.MUB6.Certificate.GramAssembly.key` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.GramAssembly.Block4.entries` (definitions bundle `OAIQ106E007` of this split); `OAI.MUB6.Certificate.Integer.Sparse.reindex` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.Certificate.GramEntries.Block4.entries` (definitions bundle `OAIQ106E032` of this split).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.GramAssembly.Block4.indexed_entry_eval_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block4Reindex13.lean (declaration OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_13)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E007
import Definitions.Def_OAIQ106E010
import Definitions.Def_OAIQ106E032

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem entries_reindex_13_e (j : Fin 22) :
    Integer.Sparse.reindex key (entries 13 j) = GramEntries.Block4.entries 13 j := by
  sorry

end MUB6.Certificate.GramAssembly.Block4

end OAI
end
