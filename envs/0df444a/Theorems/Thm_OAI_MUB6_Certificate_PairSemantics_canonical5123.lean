-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_canonical5123
-- name    : OAI.MUB6.Certificate.PairSemantics.canonical5123
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:22:29.758354+00:00
-- url     : https://prove2.me/theorems/b936d1b3-cf09-413f-b8b1-a81421a186dc
-- title:
--   OAI.MUB6.Certificate.PairSemantics.canonical5123: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.PairSemantics.canonical5123` of [lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Canonical160.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Canonical160.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.PairSemantics`):
--
--   ```lean
--   theorem canonical5123 {H : CMatrix} (_hH : IsHadamard H) :
--       injectiveMoment H raw5123 = injectiveMoment H node46
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.injectiveMoment` (definitions bundle `OAIQ106D000` of this split); `OAI.MUB6.Certificate.PairSemantics.node46` (definitions bundle `OAIQ106D043` of this split); `OAI.MUB6.Certificate.PairSemantics.raw5123` (definitions bundle `OAIQ106D060` of this split); `OAI.MUB6.CMatrix` and `OAI.MUB6.IsHadamard` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound479`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval331`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval370`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval371`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval377`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval475`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval362`, `OAI.MUB6.Certificate.PairTargetSemantics.certificate_zero1`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity0`, `OAI.MUB6.Certificate.PairTargetSemantics.partition14`, `OAI.MUB6.Certificate.PairTargetSemantics.partition19`, `OAI.MUB6.Certificate.PairTargetSemantics.partition24` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Canonical160.lean (declaration OAI.MUB6.Certificate.PairSemantics.canonical5123)

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D043
import Definitions.Def_OAIQ106D060

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5123 = injectiveMoment H node46 := by
  sorry

end MUB6.Certificate.PairSemantics

end OAI
end
