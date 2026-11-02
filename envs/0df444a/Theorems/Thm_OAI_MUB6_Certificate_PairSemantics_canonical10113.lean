-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_canonical10113
-- name    : OAI.MUB6.Certificate.PairSemantics.canonical10113
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:24:01.259958+00:00
-- url     : https://prove2.me/theorems/0818819c-a0ab-4f42-adcd-dd27d4e1db27
-- title:
--   OAI.MUB6.Certificate.PairSemantics.canonical10113: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.PairSemantics.canonical10113` of [lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Canonical316.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Canonical316.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.PairSemantics`):
--
--   ```lean
--   theorem canonical10113 {H : CMatrix} (_hH : IsHadamard H) :
--       injectiveMoment H raw10113 = injectiveMoment H node1323
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.injectiveMoment` (definitions bundle `OAIQ106D000` of this split); `OAI.MUB6.Certificate.PairSemantics.node1323` (definitions bundle `OAIQ106D042` of this split); `OAI.MUB6.Certificate.PairSemantics.raw10113` (definitions bundle `OAIQ106D055` of this split); `OAI.MUB6.CMatrix` and `OAI.MUB6.IsHadamard` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.PairTargetSemantics.partition25` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Canonical316.lean (declaration OAI.MUB6.Certificate.PairSemantics.canonical10113)

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D042
import Definitions.Def_OAIQ106D055

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical10113 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10113 = injectiveMoment H node1323 := by
  sorry

end MUB6.Certificate.PairSemantics

end OAI
end
