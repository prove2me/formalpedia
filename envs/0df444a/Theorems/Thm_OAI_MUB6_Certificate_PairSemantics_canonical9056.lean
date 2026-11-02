-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_canonical9056
-- name    : OAI.MUB6.Certificate.PairSemantics.canonical9056
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:26:44.565122+00:00
-- url     : https://prove2.me/theorems/88847e5f-453e-4f13-ac51-447e351afaa9
-- title:
--   OAI.MUB6.Certificate.PairSemantics.canonical9056: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.PairSemantics.canonical9056` of [lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Canonical283.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Canonical283.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.PairSemantics`):
--
--   ```lean
--   theorem canonical9056 {H : CMatrix} (_hH : IsHadamard H) :
--       injectiveMoment H raw9056 = injectiveMoment H node0
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.injectiveMoment` (definitions bundle `OAIQ106D000` of this split); `OAI.MUB6.Certificate.PairSemantics.node0` (definitions bundle `OAIQ106D041` of this split); `OAI.MUB6.Certificate.PairSemantics.raw9056` (definitions bundle `OAIQ106D066` of this split); `OAI.MUB6.CMatrix` and `OAI.MUB6.IsHadamard` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.PairTargetSemantics.partition12`, `OAI.MUB6.Certificate.PairTargetSemantics.partition24`, `OAI.MUB6.Certificate.PairTargetSemantics.partition25`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Canonical283.lean (declaration OAI.MUB6.Certificate.PairSemantics.canonical9056)

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D041
import Definitions.Def_OAIQ106D066

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9056 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9056 = injectiveMoment H node0 := by
  sorry

end MUB6.Certificate.PairSemantics

end OAI
end
