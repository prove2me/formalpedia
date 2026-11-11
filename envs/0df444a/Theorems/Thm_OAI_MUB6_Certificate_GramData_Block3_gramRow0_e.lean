-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow0_e
-- name    : OAI.MUB6.Certificate.GramData.Block3.gramRow0_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:16:43.467472+00:00
-- url     : https://prove2.me/theorems/9d491ff5-c5eb-4dcf-8656-d239ed26806c
-- title:
--   OAI.MUB6.Certificate.GramData.Block3.gramRow0_e: row 0 of the Block-3 Gram identity, intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   Row $0$ of the Gram identity `OAI.MUB6.Certificate.GramData.Block3.gram_e`: for every $j < 27$, the entry $Z_{0,j}$ of the Block-3 Gram matrix equals $\sum_k L_{k,0}\,D_k\,L_{k,j}$, where $L$ is the unit lower-triangular matrix built from `entries` and $D$ the diagonal. It is an intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound` (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0). OpenAI's Lean proves the full $27 \times 27$ identity in one declaration (`OAI.MUB6.Certificate.GramData.Block3.gram`, [GramData](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramData)); this row form was added to the split so that the identity is assembled from 27 rows rather than 729 entries at once, which kept the verifier's memory under its limit.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramData.Block3`, with `open Matrix`, `open scoped BigOperators`):
--
--   ```lean
--   theorem gramRow0_e : ∀ j : Fin 27, Z 0 j =
--       ∑ k, lowerUnit entries k 0 * D k * lowerUnit entries k j
--   ```
--
--   **Definitions.** `OAI.MUB6.Certificate.GramData.Block3.D`, `OAI.MUB6.Certificate.GramData.Block3.Z` and `OAI.MUB6.Certificate.GramData.Block3.entries` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.lowerUnit` (definitions bundle `OAIQ106E147` of this split).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.GramData.Block3.gram_e` imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramData (declaration OAI.MUB6.Certificate.GramData.Block3.gram, row 0)

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

theorem gramRow0_e : ∀ j : Fin 27, Z 0 j =
    ∑ k, lowerUnit entries k 0 * D k * lowerUnit entries k j := by
  sorry

end MUB6.Certificate.GramData.Block3

end OAI
end
