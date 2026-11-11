-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramNonnegative_sourceGram_nonneg_e
-- name    : OAI.MUB6.Certificate.GramNonnegative.sourceGram_nonneg_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T19:35:47.35408+00:00
-- url     : https://prove2.me/theorems/f5f68e60-2297-4477-9260-ec638d2df4c7
-- title:
--   OAI.MUB6.Certificate.GramNonnegative.sourceGram_nonneg_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramNonnegative.sourceGram_nonneg` of [lean/OAI/Analysis/MutuallyUnbiased/Certificate/GramNonnegative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Certificate/GramNonnegative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramNonnegative`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem sourceGram_nonneg_e (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
--       0 ≤ sourceGram B
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.GramNonnegative.sourceGram` (definitions bundle `OAIQ106E042` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Certificate/GramNonnegative.lean (declaration OAI.MUB6.Certificate.GramNonnegative.sourceGram_nonneg)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E042

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramNonnegative

theorem sourceGram_nonneg_e (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    0 ≤ sourceGram B := by
  sorry

end MUB6.Certificate.GramNonnegative

end

end OAI
end
